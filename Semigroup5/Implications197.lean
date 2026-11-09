import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53958_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53958 : Equation53958 G) : Equation53901 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h53958 X2 X1 X0]
    conv => enter [1]; rw [← h53958 X1 X2 X2]
  have l4 : ∀ X2 X0 X1 : G, ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53958 (X2 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h53958 X0 X1 X2]
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h53958 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53958 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53958 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l8 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53958 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l9 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53958 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 ((sK0 ◇ sK1) ◇ X0)]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l4 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 X0 ((X2 ◇ X0) ◇ X2)]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l10 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l11 X1 X0 X2]
    conv => enter [1]; rw [l3 X2 X0 X2]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ X0) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53958 X0 sK1 sK1]
    conv => enter [1]; rw [h53958 sK1 (sK1 ◇ X0) sK0]
  have l14 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [h53958 sK1 X0 sK0]
  have l15 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l14 sK1 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l13 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (sK0 ◇ sK1)]
  have l17 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l15 sK1 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l18 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l16 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) = (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← l17 sK1 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l20 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l19 sK0 X0 sK1 X1]
    conv => enter [1]; rw [h53958 sK1 (X0 ◇ X1) sK0]
  have l21 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l20 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) sK2 sK0]
  have l23 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53958 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) sK0]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) = ((sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [h53958 (sK0 ◇ sK1) X0 sK0]
  have l25 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l24 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l23 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l25 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l29 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l26 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l30 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [← l28 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l31 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l30 sK0 X0 sK1 X1]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) (X0 ◇ X1) sK0]
  have l32 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l31 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h53958 X0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [h53958 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0) sK0]
  have l34 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [h53958 (sK1 ◇ sK2) X0 sK0]
  have l35 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l34 sK1 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l36 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l33 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l37 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l35 sK1 sK2 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l38 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l36 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l39 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [← l37 sK1 sK2 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l40 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1))) = (sK0 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [l39 sK0 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h53958 (sK1 ◇ sK2) (X0 ◇ X1) sK0]
  have l41 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [l40 sK0 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53958 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK1) sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK1) sK0 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ sK0)]
    conv => enter [1, 2]; rw [l6 (sK1 ◇ sK2) sK0 sK1]
  have l45 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ (X0 ◇ sK0)) ◇ X1) = (sK1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 1]; rw [l6 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ sK1) ◇ X0) X1]
  have l46 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l45 X0 sK0 X1 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← h53958 (sK0 ◇ sK1) sK1 (sK0 ◇ sK1)]
  have l50 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l46 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ sK0) X1]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) (sK1 ◇ sK2) sK0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l18 (sK0 ◇ sK1) sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) sK1 sK0]
  have l54 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l50 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l55 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l51 sK0 sK1 sK2]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) sK1 sK0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l57 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK0 sK1]
    conv => enter [1]; rw [← l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l63 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l61 sK0 sK1]
  have l64 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53958 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l55 sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1]; rw [← l65 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l67 sK0 sK1 sK2]
    conv => enter [1]; rw [l64 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53958 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l58 sK0 sK1]
  have l70 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l58 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK0) X0]
  have l71 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l70 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l73 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l71 sK0 sK1 X0]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l62 sK0 sK1]
    conv => enter [1]; rw [l72 sK0 sK1]
  have l75 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l64 sK0 sK1 X0]
    conv => enter [1]; rw [l73 sK0 sK1 X0]
  have l76 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l61 sK0 sK1]
  have l77 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (((sK0 ◇ sK1) ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l12 ((sK0 ◇ sK1) ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [l58 sK0 sK1]
  have l78 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X2)) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l12 (X1 ◇ X0) X1 X2]
    conv => enter [1, 2]; rw [← h53958 X0 X1 X1]
  have l79 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [← l12 X0 sK2 X1]
    conv => enter [1, 2]; rw [h53958 sK2 X0 sK1]
  have l80 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ sK0)]
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ sK2) X0]
  have l81 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ ((X1 ◇ (X1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [← h53958 sK1 (X1 ◇ (X1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l12 sK1 X1 X0]
  have l82 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ ((X1 ◇ (X1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [← l12 (sK0 ◇ sK1) X1 X0]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) (X1 ◇ (X1 ◇ (sK0 ◇ sK1))) sK0]
  have l83 : ∀ sK0 X1 sK1 sK2 X0 : G, (sK0 ◇ ((X1 ◇ (X1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X1 sK1 sK2 X0
    conv => enter [1]; rw [← h53958 (sK1 ◇ sK2) (X1 ◇ (X1 ◇ (sK1 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [l12 (sK1 ◇ sK2) X1 X0]
  have l84 : ∀ X2 X3 X0 X1 : G, (X2 ◇ ((X2 ◇ X2) ◇ X3)) = ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X3) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h4512 X2 (X2 ◇ X2) X3]
    conv => enter [1, 1]; rw [← l12 X0 X1 X2]
  have l85 : ∀ X2 X3 X0 X1 : G, (X2 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l84 X2 X3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X3]
  have l86 : ∀ sK1 sK2 X0 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X1 ◇ ((X1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1]; rw [← l83 sK0 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l87 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X1 ◇ ((X1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l82 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l88 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X1 ◇ ((X1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [← l81 sK0 X1 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ sK1) (sK0 ◇ sK1)]
  have l89 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [l80 sK0 sK1 sK2 X0]
  have l90 : ∀ X1 sK1 sK2 : G, (X1 ◇ (X1 ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [l79 X1 X1 sK1 sK2]
    conv => enter [1]; rw [← h53958 (sK1 ◇ sK2) sK1 X1]
  have l91 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l78 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l92 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l77 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l93 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l75 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l76 X0 sK0 sK1]
  have l94 : ∀ X2 X3 X0 X1 : G, (X2 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l85 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X3]
  have l95 : ∀ sK1 sK2 X0 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1]; rw [l86 sK1 sK2 X0 sK0 X1]
    conv => enter [1]; rw [← l41 sK0 X1 sK1 sK2 (X1 ◇ (sK1 ◇ sK2))]
  have l96 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l87 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l32 sK0 X1 sK1 (X1 ◇ (sK0 ◇ sK1))]
  have l97 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ sK1)))) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [l88 sK1 X0 sK0 X1]
    conv => enter [1]; rw [← l21 sK0 X1 sK1 (X1 ◇ sK1)]
  have l98 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← h53958 (sK1 ◇ sK2) sK1 sK0]
    conv => enter [1]; rw [← l90 X1 sK1 sK2]
  have l99 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0 X0]
    conv => enter [1]; rw [← l91 X2 X1 X0]
  have l100 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l92 X0 sK0 sK1]
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l101 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l89 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l93 sK0 sK1 sK0]
  have l102 : ∀ X2 X3 X0 X1 : G, (X2 ◇ ((X2 ◇ X2) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l94 X2 X3 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l103 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l95 sK1 sK2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h53958 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l104 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l96 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h53958 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l105 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l97 sK1 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h53958 sK1 (sK0 ◇ sK1) sK1]
  have l106 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l98 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l89 sK0 sK1 sK2 sK0]
  have l107 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l99 X0 X1 X0]
    conv => enter [1]; rw [← l89 sK0 sK1 sK2 X0]
  have l108 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l100 X0 sK0 sK1]
    conv => enter [1]; rw [← l54 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l109 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l101 sK0 sK1 sK2]
    conv => enter [1]; rw [← l74 sK0 sK1]
  have l110 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X3)))) = (X2 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l102 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X2 X3]
  have l111 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l103 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l112 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l104 sK0 sK1 X0]
  have l113 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l105 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l114 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l106 sK0 sK1 sK2]
  have l115 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l108 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l64 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l116 : ∀ sK0 sK1 sK2 X0 X1 X3 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro sK0 sK1 sK2 X0 X1 X3
    conv => enter [1]; rw [← l107 sK0 (sK0 ◇ X3) sK0 sK1 sK2]
    conv => enter [1]; rw [← l110 X0 X1 X3 sK0]
  have l117 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l38 (sK1 ◇ sK2) sK1 sK2 sK1]
    conv => enter [1]; rw [← l111 sK1 sK2 X0 sK1]
  have l118 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l89 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l112 sK0 sK1 sK0]
  have l119 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l18 sK1 sK1 sK1]
    conv => enter [1]; rw [← l113 sK1 X0 sK1]
  have l120 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l114 sK0 sK1 sK2]
  have l121 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l115 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l68 sK0 sK1 sK2]
  have l122 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l116 sK0 sK1 sK2 X0 sK0 sK0]
    conv => enter [1, 2]; rw [l107 sK0 (X0 ◇ sK0) sK0 sK1 sK2]
  have l123 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l89 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l117 sK1 sK2 sK1]
  have l124 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [← l118 sK0 sK1 sK2]
  have l125 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l89 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l119 sK1 sK1]
  have l126 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [← l107 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1]; rw [← l121 X0 sK1 sK0 sK2]
  have l127 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l109 sK0 sK1 sK0]
    conv => enter [1]; rw [l122 sK0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l109 sK0 sK1 sK0]
  have l128 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l123 sK1 sK2 sK0]
    conv => enter [1]; rw [h53958 (sK1 ◇ sK2) (sK1 ◇ sK2) sK0]
  have l129 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l124 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l130 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l125 sK1 sK0 sK2]
    conv => enter [1]; rw [h53958 sK1 sK1 sK0]
  have l131 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l89 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l126 sK1 sK0 sK2 sK0]
  have l132 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l128 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l133 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 (sK0 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [l129 sK0 sK1 sK2]
  have l134 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l130 sK1 sK0 sK2]
  have l135 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l131 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1))]
  have l136 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1]; rw [l132 sK1 sK2 sK0]
  have l137 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53958 (sK0 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [l133 sK0 sK1 sK2]
  have l138 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l134 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1))]
  have l139 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l109 sK0 sK1 sK2]
    conv => enter [1]; rw [l135 sK0 sK1 sK2]
  have l140 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [l136 sK0 sK1 sK2]
  have l141 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l137 sK0 sK1 sK2]
  have l142 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l139 sK0 sK1 sK0]
    conv => enter [1]; rw [← l138 sK0 sK1 sK0]
  have l143 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l64 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l140 sK0 sK1 sK2]
  have l144 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l141 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l138 sK0 sK1 sK0]
  have l145 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [l143 sK0 sK1 sK2]
  have l146 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l144 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l147 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l142 sK0 sK1]
    conv => enter [1]; rw [l145 sK0 sK1 sK2]
  have l148 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l146 sK0 sK1]
  have l149 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l120 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l150 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l120 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l151 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l150 sK0 sK1 sK2 X0]
  have l152 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l149 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l138 sK0 sK1 sK2]
  have l153 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l152 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l154 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l148 sK0 sK1]
    conv => enter [1]; rw [← l153 sK0 sK1 sK2]
  have l155 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l147 sK0 sK1 sK2]
    conv => enter [1]; rw [h53958 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l156 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l155 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l157 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) sK2 sK0 sK1]
    conv => enter [1]; rw [l156 sK0 sK1 sK2]
  have l158 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h53958 (sK0 ◇ sK1) sK2 sK0]
    conv => enter [1]; rw [l157 sK0 sK1 sK2]
  have l159 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [l158 sK0 sK2 sK1]
  have l160 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l159 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l161 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l160 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l107 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK0 sK1 sK2]
  have l162 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l161 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l109 sK0 sK1 sK2]
  have l163 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l162 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l142 sK0 sK1]
  have l164 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l163 sK0 sK1 sK2 X0]
  have l165 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h53958 (sK0 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l109 sK0 sK1 sK2]
  have l166 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l109 sK0 sK1 sK2]
  have l167 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l166 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l168 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l165 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l127 sK0 sK1 X0]
  have l169 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l167 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l107 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0 sK1 sK2]
  have l170 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l168 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l151 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l171 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l169 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l109 sK0 sK1 sK2]
  have l172 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l164 sK0 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l170 sK0 sK1 X0 sK0]
  have l173 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l171 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l142 sK0 sK1]
  have l174 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l107 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l172 sK0 sK1 sK0]
  have l175 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l120 sK0 sK1 sK2]
    conv => enter [1]; rw [l174 sK0 sK1 sK2]
  have l176 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l175 sK0 sK1 sK2]
    conv => enter [1]; rw [h53958 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l177 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l175 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l178 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l177 sK0 sK1 sK2]
    conv => enter [1]; rw [← l148 sK0 sK1]
  have l179 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l176 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l180 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l178 sK0 sK1 sK2]
    conv => enter [1]; rw [l107 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
  have l181 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l179 sK0 sK1 sK2]
    conv => enter [1]; rw [l142 sK0 sK1]
  have l182 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l175 sK0 sK1 sK2]
    conv => enter [1]; rw [← l181 sK0 sK1 sK2]
  have l183 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l182 sK0 sK1 sK2]
    conv => enter [1]; rw [← l154 sK0 sK1 sK2]
  have l184 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l107 sK0 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l180 sK0 sK1 sK0]
  have l185 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l107 sK0 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l186 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l185 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l173 sK0 sK1 sK0 X0]
  have l187 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l186 sK0 sK1 X0]
    conv => enter [1]; rw [← l175 sK0 sK1 sK2]
  have l188 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l187 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l183 sK0 sK1 sK0]
  have l189 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l184 sK0 sK1]
    conv => enter [1]; rw [← l188 sK0 sK1 X0]
  have l190 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53958 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l189 sK0 sK1 (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))]
  have l191 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l190 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l6 X0 sK0 sK1]
  have l192 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l191 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l192 x y z]

theorem Equation4512_53901_implies_Equation53961 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53961 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53901 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l1 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l2 sK1 sK2 X1 sK1]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l3 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h53901 (sK1 ◇ (sK1 ◇ sK2)) X0 X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [← l4 X0 sK1 sK2]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53901 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 X1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 X1]
  have l9 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l9 z y w x y]

theorem Equation4512_53961_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53961 : Equation53961 G) : Equation53901 G := by
  have l0 : ∀ sK0 X0 sK1 X2 X3 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X2 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 X0 sK1 X2 X3
    conv => enter [1]; rw [← h53961 sK0 X0 sK0 sK1]
    conv => enter [1]; rw [h53961 sK0 X0 X2 X3]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53961 X0 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK0 X1 sK1 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l0 sK0 X1 sK1 sK0 (X1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK1 sK0 X1]
  have l5 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 X1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK0]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h53961 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [h53961 sK1 sK0 sK0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_53901_implies_Equation53994 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53994 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53901 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l1 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ sK2) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l1 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l3 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l2 sK1 sK2 X1 sK1]
  have l4 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l3 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h53901 (sK1 ◇ (sK1 ◇ sK2)) X0 X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [← l4 X0 sK1 sK2]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53901 X0 X1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK2 X1]
  have l7 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 X1]
  have l9 : ∀ X1 X0 X2 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 sK1 sK2
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l9 z w x x y]

theorem Equation4512_53994_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53994 : Equation53994 G) : Equation53901 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53994 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 ((sK0 ◇ sK1) ◇ X0)]
  have l2 : ∀ sK1 X1 sK2 sK0 : G, (sK1 ◇ (X1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK1 X1 sK2 sK0
    conv => enter [1]; rw [← h53994 sK2 sK1 sK1 X1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0 sK1 sK2]
  have l3 : ∀ sK1 X1 sK2 sK0 : G, (sK1 ◇ (X1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 X1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK1 sK2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l5 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK1 sK0 sK2 sK0]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  have l7 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK2) sK2 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK0 sK2]
  have l10 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l12 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK1 (sK0 ◇ (sK1 ◇ sK2)) sK2 sK0]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l14 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l15 : ∀ sK1 sK2 X0 sK0 X1 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h53994 sK1 (sK2 ◇ X0) sK0 X1]
  have l16 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l14 sK1 sK0 sK2]
    conv => enter [1]; rw [h53994 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0 X0]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53994 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0 sK2 sK1]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0 sK1 sK1]
    conv => enter [1]; rw [← h53994 sK1 sK2 sK1 sK1]
  have l19 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK2]
    conv => enter [1]; rw [← l17 sK1 sK2 sK0]
  have l20 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l19 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
  have l21 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l18 sK1 sK2 X0]
  have l22 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK0 sK2]
    conv => enter [1]; rw [← l21 sK1 sK0 sK2 X0]
  have l23 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h53994 X0 X1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [← l22 sK1 sK0 sK2 (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))]
  intro x y z
  conv => enter [1]; rw [l23 x y y x z]

theorem Equation4512_53901_implies_Equation53998 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53901 : Equation53901 G) : Equation53998 G := by
  have l0 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK3 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h53901 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK3 X0]
  have l1 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1) = (sK3 ◇ (((sK2 ◇ sK3) ◇ X0) ◇ X1)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1, 1]; rw [l0 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 sK3 ((sK2 ◇ sK3) ◇ X0) X1]
  have l2 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1) = (sK3 ◇ ((sK2 ◇ sK3) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l1 sK2 sK3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK3) X0 X1]
  have l3 : ∀ sK2 sK3 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ X1) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [l0 sK2 sK3 (sK2 ◇ X1)]
    conv => enter [1]; rw [← l2 sK2 sK3 X1 sK2]
  have l4 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro X0 sK2 sK3
    conv => enter [1, 2]; rw [l3 sK2 sK3 (X0 ◇ X0)]
    conv => enter [1]; rw [← h53901 (sK2 ◇ (sK2 ◇ sK3)) X0 X0]
  have l5 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l3 sK2 sK3 ((sK2 ◇ (sK2 ◇ sK3)) ◇ X0)]
    conv => enter [1]; rw [← l4 X0 sK2 sK3]
  have l6 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h53901 X0 X1 (sK2 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [← l5 sK2 sK3 X1]
  have l7 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l6 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [← l5 sK2 sK3 X0]
  have l8 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l7 X0 X1 sK2 sK3]
    conv => enter [1]; rw [← l5 sK2 sK3 X1]
  have l9 : ∀ X1 X0 X2 sK2 sK3 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 X2 sK2 sK3
    conv => enter [1]; rw [← h53901 X0 X1 X2]
    conv => enter [1]; rw [l8 X0 X1 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [← l9 z w u x y]

@[equational_result]
theorem Equation53998_implies_Equation53901 (G : Type*) [Magma G] (h53998 : Equation53998 G) : Equation53901 G := by
  have l0 : ∀ X3 X4 X5 sK0 X0 sK1 : G, (X3 ◇ (X4 ◇ (X3 ◇ X5))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X3 X4 X5 sK0 X0 sK1
    conv => enter [1]; rw [← h53998 X3 X3 X3 X4 X5]
    conv => enter [1]; rw [h53998 X3 X3 sK0 X0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53998 sK0 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [h53998 sK0 (sK0 ◇ sK1) sK0 X0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X3 X4 X5 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X3 ◇ (X4 ◇ (X3 ◇ X5))) := by
    intro sK0 sK1 X3 X4 X5
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 X3 X4 X5 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y y x z]

theorem Equation4512_53902_implies_Equation53918 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation53918 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53902 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h53902 X0 (X1 ◇ X0) X1]
  have l1 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h53902 sK1 X0 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK2)) sK1]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53902 X0 X1 X2]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53902 sK1 sK0 X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h53902 (sK0 ◇ sK1) sK0 X0]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l2 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h53902 X0 X0 X1]
  have l7 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l8 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [← h53902 X0 X2 X0]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l7 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l8 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ X2)]
  have l11 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l9 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2 X1]
    conv => enter [1]; rw [← l12 X0 X2 X1]
  have l14 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h53902 sK2 X0 sK2]
    conv => enter [1, 2]; rw [h53902 sK2 sK2 sK0]
  have l15 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h53902 sK2 sK2 X0]
    conv => enter [1]; rw [h53902 sK2 (X0 ◇ sK2) sK0]
  have l16 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l15 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 sK2 (sK2 ◇ (sK0 ◇ sK2))]
  have l17 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h53902 sK2 X0 sK0]
    conv => enter [1]; rw [l14 sK2 X0 sK0]
  have l18 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h53902 sK2 sK2 sK0]
    conv => enter [1]; rw [l16 sK2 X0 sK0]
  have l19 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← h53902 sK2 (sK0 ◇ sK2) sK0]
  have l20 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l19 sK0 sK2 X0]
  have l21 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h53902 (sK2 ◇ (sK0 ◇ sK2)) X0 sK2]
    conv => enter [1, 2]; rw [← l17 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK0]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK2 ◇ (sK0 ◇ sK2))]
  have l23 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h53902 sK2 (sK2 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l17 sK2 sK2 sK0]
  have l24 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l21 sK2 sK0 X0]
    conv => enter [1, 2]; rw [l23 sK2 sK0]
  have l25 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l24 sK2 sK0 X0]
    conv => enter [1]; rw [← l17 X0 sK2 sK0]
  have l26 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← h53902 sK2 (sK0 ◇ sK2) sK0]
  have l27 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l28 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK2 X0]
    conv => enter [1]; rw [← l20 sK2 sK0 X0]
  have l29 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [l28 sK0 sK2 X0]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l23 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
  have l31 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l23 sK2 sK0]
  have l32 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l31 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
  have l34 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l29 sK0 sK2 X0]
    conv => enter [1]; rw [← l32 sK2 sK0 X0]
  have l35 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK2 X0]
    conv => enter [1]; rw [l25 sK2 sK0 X0]
  have l36 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l17 X0 sK2 sK0]
    conv => enter [1]; rw [← l18 sK2 sK0 X0]
  have l37 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l36 X0 sK2 sK0]
    conv => enter [1]; rw [← l36 X1 sK2 sK0]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l36 (sK0 ◇ sK1) sK2 sK0]
  have l39 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [l36 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK2 sK0]
  have l40 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [← l36 X0 sK2 sK0]
  have l41 : ∀ X0 sK2 sK0 X1 : G, ((X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1, 1]; rw [l36 X0 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK2)) X1]
  have l42 : ∀ X0 sK2 sK0 X1 : G, ((X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l41 X0 sK2 sK0 X1]
    conv => enter [1]; rw [← l29 sK0 sK2 X1]
  have l43 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK0]
    conv => enter [1]; rw [← l40 sK0 sK2 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK0 sK2]
  have l45 : ∀ X0 sK2 sK0 X1 : G, ((X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l42 X0 sK2 sK0 X1]
    conv => enter [1]; rw [l35 sK0 sK2 X1]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2 sK0]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2]
  have l47 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1)) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ (sK0 ◇ sK2)) X1]
    conv => enter [1]; rw [l45 X0 sK2 sK0 X1]
  have l48 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l46 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
  have l49 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l43 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l50 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l49 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l47 sK0 sK2 sK0 X0]
  have l51 : ∀ X0 sK2 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK2 sK0 X1 X2
    conv => enter [1]; rw [l37 X0 sK2 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ (sK0 ◇ sK2))]
  have l52 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [l37 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK2 sK0 X0]
  have l53 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [l51 X0 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [l52 X0 sK2 sK0 sK1]
  have l54 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l53 sK1 sK2 sK0 X1 sK1]
  have l55 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ X0) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h53902 (sK1 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2]; rw [h53902 sK1 X0 sK0]
  have l56 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h53902 sK1 (X0 ◇ X1) sK0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53902 sK1 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53902 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 sK1]
    conv => enter [1]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l61 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l56 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 X0 X1]
  have l62 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (X1 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l55 sK1 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l60 sK0 sK1]
  have l65 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l62 sK1 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [l61 X0 X0 sK1 sK1]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← h53902 sK1 (sK0 ◇ sK1) sK0]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [← h53902 sK1 (sK0 ◇ sK1) sK0]
  have l68 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (sK1 ◇ (sK1 ◇ (X1 ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l65 sK1 X0 X1]
    conv => enter [1]; rw [← l11 sK1 X1 X0 sK1]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← h53902 sK1 sK1 sK0]
  have l70 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0]
    conv => enter [1]; rw [← h53902 sK1 sK1 sK0]
  have l71 : ∀ sK1 X0 X1 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ X1)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l68 sK1 X0 X1]
    conv => enter [1]; rw [l13 sK1 X1 X0]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l69 sK0 sK1]
    conv => enter [1]; rw [h53902 (sK0 ◇ sK1) sK0 sK0]
  have l73 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l70 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 sK0]
  have l74 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ X0) ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l71 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK1 ◇ X0) ◇ X1)]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l76 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l73 sK1 sK0 sK2]
  have l77 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l74 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X0 X1]
  have l78 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l76 sK1 sK2 sK0]
    conv => enter [1]; rw [l75 sK1 sK0]
  have l79 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l77 sK1 X0 X1]
    conv => enter [1]; rw [← l11 X0 sK1 X1 sK1]
  have l80 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l50 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [l78 sK1 sK2 sK0]
  have l81 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← l13 X0 sK1 X1]
    conv => enter [1]; rw [← l79 sK1 X0 X1]
  have l82 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l80 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l83 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l82 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l81 (sK0 ◇ (sK0 ◇ sK1)) X0 sK1]
  have l84 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l83 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l81 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l85 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l84 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l75 sK1 sK0]
  have l86 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l80 sK1 sK2 sK0]
    conv => enter [1]; rw [← l85 sK1 sK2 sK0 X0]
  have l87 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [h53902 X0 X1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← l86 sK1 sK2 sK0 X0]
  have l88 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l87 X0 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l54 sK1 sK2 sK0 X0]
  have l89 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l88 X0 X1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l54 sK1 sK2 sK0 X1]
  intro x y z
  conv => enter [1]; rw [l89 x y y z x]

theorem Equation4512_53918_implies_Equation53902 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53918 : Equation53918 G) : Equation53902 G := by
  have l0 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h53918 sK2 X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l1 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h53918 (sK2 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h53918 X0 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (X0 ◇ (sK2 ◇ sK0))]
  have l3 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l0 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l2 (sK2 ◇ sK0) sK0 sK2]
  have l4 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l3 sK2 X0 sK0]
    conv => enter [1, 2]; rw [l1 sK2 sK0 sK0]
  have l5 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l4 sK2 X0 sK0]
    conv => enter [1]; rw [← h53918 (sK0 ◇ (sK2 ◇ sK0)) X0 sK0]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l5 sK2 X0 sK0]
    conv => enter [1]; rw [h53918 sK2 X0 sK0]
  have l7 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h53918 sK2 X0 sK2]
    conv => enter [1, 2]; rw [h53918 sK2 sK2 sK0]
  have l8 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (sK2 ◇ X0)) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l7 sK2 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l9 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h53918 sK2 X0 sK0]
    conv => enter [1]; rw [l8 sK2 X0 sK0]
  have l10 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l9 sK2 sK0 sK2]
    conv => enter [1]; rw [h53918 sK2 ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) sK0]
  have l11 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l10 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53918 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK2 sK0]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [h53918 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l14 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h53918 (sK0 ◇ (sK2 ◇ sK0)) X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK2]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53918 sK0 X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l14 sK0 sK2 X0]
  have l16 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l15 sK0 X0 sK2]
    conv => enter [1]; rw [l6 sK0 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation4512_53902_implies_Equation53930 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation53930 G := by
  have l0 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [h53902 sK3 X0 sK3]
    conv => enter [1, 2]; rw [h53902 sK3 sK3 sK0]
  have l1 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((X0 ◇ sK3) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [h53902 sK3 sK3 X0]
    conv => enter [1]; rw [h53902 sK3 (X0 ◇ sK3) sK0]
  have l2 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [l1 sK3 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 sK3 (sK3 ◇ (sK0 ◇ sK3))]
  have l3 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← h53902 sK3 X0 sK0]
    conv => enter [1]; rw [l0 sK3 X0 sK0]
  have l4 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h53902 sK3 sK3 sK0]
    conv => enter [1]; rw [l2 sK3 X0 sK0]
  have l5 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h53902 sK3 (sK3 ◇ (sK0 ◇ sK3)) sK0]
    conv => enter [1]; rw [← l3 sK3 sK3 sK0]
  have l6 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l5 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK3)) (sK3 ◇ (sK0 ◇ sK3))]
  have l7 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK0]
    conv => enter [1]; rw [l6 sK2 sK3 sK0]
  have l8 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l3 X0 sK3 sK0]
    conv => enter [1]; rw [← l4 sK3 sK0 X0]
  have l9 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l4 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l10 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l9 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l3 X1 sK3 sK0]
  have l11 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK2 sK3 sK0]
    conv => enter [1]; rw [l8 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK3 sK0]
  have l12 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK2 sK3 sK0]
  have l13 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [l3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [← l11 sK2 sK3 sK0]
  have l14 : ∀ sK2 sK3 sK0 X1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1) = (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1)) := by
    intro sK2 sK3 sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) X1]
  have l15 : ∀ sK2 sK3 sK0 X1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1)) = (X1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK2 sK3 sK0 X1 X0
    conv => enter [1]; rw [h53902 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) X1 X0]
    conv => enter [1, 2, 2]; rw [← l13 X0 sK3 sK0 sK2]
  have l16 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l14 sK2 sK3 sK0 (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) X1]
    conv => enter [1]; rw [← l15 sK2 sK3 sK0 X1 X0]
  have l17 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l16 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l14 sK2 sK3 sK0 X1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l18 : ∀ sK3 sK0 sK2 X1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1) := by
    intro sK3 sK0 sK2 X1
    conv => enter [1]; rw [l10 sK3 sK0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK3]
    conv => enter [1]; rw [l17 sK2 sK3 sK0 sK3 X1]
  have l19 : ∀ sK2 sK3 sK0 X1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X1) := by
    intro sK2 sK3 sK0 X1
    conv => enter [1]; rw [l11 sK2 sK3 sK0]
    conv => enter [1]; rw [l18 sK3 sK0 sK2 X1]
  have l20 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h53902 X0 X1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1, 2, 2]; rw [← l19 sK2 sK3 sK0 X0]
  have l21 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l20 X0 X1 X0 sK3 sK0]
    conv => enter [1, 2]; rw [← l13 X0 sK3 sK0 X0]
  have l22 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l21 X0 X1 sK3 sK0]
    conv => enter [1]; rw [← l10 sK3 sK0 X1 X0]
  have l23 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 X0 X1 sK3 sK0]
    conv => enter [1]; rw [← l11 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l23 x y y z w]

@[equational_result]
theorem Equation53930_implies_Equation53902 (G : Type*) [Magma G] (h53930 : Equation53930 G) : Equation53902 G := by
  intro x y z
  conv => enter [1]; rw [h53930 x y x z]

theorem Equation4512_53902_implies_Equation53937 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation53937 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53902 sK1 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 sK1]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53902 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h53902 X0 (X1 ◇ X0) X1]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53902 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l8 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53902 X0 X1 X2]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53902 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53902 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h53902 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l13 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l8 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l15 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1, 2]; rw [← h53902 X0 X0 X1]
  have l16 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l13 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l17 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l15 X1 X0 X2]
    conv => enter [1]; rw [← h53902 X0 X2 X0]
  have l18 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l16 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l19 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l17 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ X2)]
  have l20 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l18 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l21 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l19 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2 X1]
    conv => enter [1]; rw [← l21 X0 X2 X1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53902 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← h53902 sK1 (sK0 ◇ sK1) sK0]
  have l27 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h53902 sK1 (X0 ◇ X1) sK0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53902 sK1 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53902 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ sK1)]
  have l32 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 X0 X1]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK1 X0]
    conv => enter [1]; rw [← l5 sK1 X0 sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK0 sK1 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← h53902 sK1 (sK0 ◇ sK1) sK0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [l33 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← h53902 sK1 sK1 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [l32 sK1 sK1 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l44 sK1 sK0]
    conv => enter [1]; rw [l43 sK1 sK0]
  have l46 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53902 sK0 sK0 X0]
    conv => enter [1]; rw [l14 sK0 (X0 ◇ sK0) sK1]
  have l47 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4512 X0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l46 sK0 X0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ sK0) sK1]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l14 sK0 sK0 sK1]
    conv => enter [1]; rw [← l47 X0 sK0 sK1]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l48 sK0 sK1]
  have l51 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53902 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l50 sK0 sK1 sK0]
  have l52 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l50 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK1 X0]
    conv => enter [1]; rw [← l52 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l53 sK0 sK1 X0]
    conv => enter [1]; rw [l45 sK0 sK1]
  have l55 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 X0]
  have l56 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l55 sK0 sK1 X0]
    conv => enter [1]; rw [← l52 sK0 sK1 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l57 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53902 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l56 sK0 sK1 X0]
  have l58 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l57 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l50 sK0 sK1 X0]
  have l59 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l58 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l50 sK0 sK1 X1]
  have l60 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l59 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [l14 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l60 x y z]

theorem Equation4512_53937_implies_Equation53902 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53937 : Equation53937 G) : Equation53902 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X3 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53937 (X0 ◇ (X1 ◇ X0)) X2 X3]
    conv => enter [1, 2, 2]; rw [← h53937 X0 X1 X2]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h53937 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53937 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53937 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X1 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53937 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53937 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X0))]
  have l8 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h53937 sK0 X0 sK2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h53937 X0 X1 X0]
  have l10 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l6 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X3 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X0 ◇ X1))]
  have l13 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l10 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l14 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l11 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l16 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l13 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l14 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← l3 X1 X2 X0 X0]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← l9 X0 (X0 ◇ X1) X1]
  have l19 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l16 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2 X0]
    conv => enter [1]; rw [← l9 X1 (X2 ◇ X0) X0]
  have l21 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l9 X0 X1 X0]
  have l22 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l19 X1 X2 X0 X2]
    conv => enter [1]; rw [l20 X2 X1 X0]
  have l23 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← l19 X0 X0 X1 X0]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X0]
    conv => enter [1]; rw [← l23 X0 X1 X2]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ X2)]
  have l26 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l25 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ X2)]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l26 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l28 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l27 X0 X1 X2]
    conv => enter [1, 2]; rw [← l9 X0 ((X1 ◇ X0) ◇ X2) X1]
  have l29 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l28 X0 X1 X2]
    conv => enter [1]; rw [← l9 X0 ((X1 ◇ X0) ◇ X2) X0]
  have l30 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l29 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l31 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l30 X0 X1 X2]
    conv => enter [1]; rw [← l19 X0 X1 X2 X0]
  have l32 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK1) ◇ sK0)]
  have l33 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) ((sK0 ◇ sK1) ◇ sK0)]
  have l35 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l1 sK2 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l36 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l36 sK1 sK0 sK0]
  have l38 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l35 sK2 sK0 sK1]
    conv => enter [1]; rw [l22 (sK2 ◇ sK0) (sK0 ◇ sK1) sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l34 sK0 sK1 sK0]
  have l40 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l33 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK1]
  have l41 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l32 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK0]
  have l42 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l38 sK2 sK0 sK1]
    conv => enter [1]; rw [← l31 (sK2 ◇ sK0) sK0 (sK0 ◇ sK1)]
  have l43 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l40 sK2 sK0 sK1]
  have l44 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l42 sK2 sK0 sK1]
    conv => enter [1]; rw [l8 sK2 sK0 (sK2 ◇ sK0)]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l43 sK2 sK0 sK1]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [l44 sK2 sK0 sK1]
  have l47 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l48 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l47 sK2 sK0 sK1]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [l48 sK2 sK0 sK1]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
  have l52 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l52 sK1 sK0 sK2]
  have l54 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h53937 sK0 sK2 X0]
    conv => enter [1]; rw [h53937 sK0 sK2 X1]
  have l55 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [l54 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 sK2 X0]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l54 sK0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l56 x y z]

theorem Equation4512_53902_implies_Equation53945 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation53945 G := by
  have l0 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53902 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) sK1]
  have l1 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ X0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h53902 sK1 ((sK1 ◇ sK2) ◇ X0) sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53902 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h53902 sK1 sK1 sK0]
  have l3 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53902 sK1 sK1 X0]
    conv => enter [1]; rw [h53902 sK1 (X0 ◇ sK1) sK0]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l3 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h53902 sK1 X0 sK0]
    conv => enter [1]; rw [l2 sK1 X0 sK0]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l1 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 (sK1 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h53902 sK1 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 X0 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53902 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l5 sK1 sK1 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l5 (sK1 ◇ sK2) sK1 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 sK1 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l10 sK1 sK2 sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0]
    conv => enter [1]; rw [h53902 sK1 sK1 sK0]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53902 sK1 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l15 : ∀ sK3 sK1 sK0 : G, ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l8 sK1 sK0]
  have l16 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l5 sK3 sK1 sK0]
    conv => enter [1]; rw [← l15 sK3 sK1 sK0]
  have l17 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l5 X0 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0 X0]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53902 sK1 sK2 sK0]
    conv => enter [1]; rw [l17 sK2 sK1 sK0]
  have l19 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l16 sK3 sK1 sK0]
    conv => enter [1]; rw [l17 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 sK0]
  have l20 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l17 X0 sK1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK2 sK0]
  have l21 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l19 sK3 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 sK1 sK0 sK2]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2 sK1]
    conv => enter [1]; rw [l20 sK1 sK1 sK1 sK2]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l21 sK3 sK1 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l23 x y z w]

@[equational_result]
theorem Equation53945_implies_Equation53902 (G : Type*) [Magma G] (h53945 : Equation53945 G) : Equation53902 G := by
  intro x y z
  conv => enter [1]; rw [h53945 x y y z]

theorem Equation4512_53902_implies_Equation53987 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation53987 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53902 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h53902 X0 (X1 ◇ X0) X1]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53902 X0 X1 X2]
  have l4 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l5 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h53902 X0 X0 X1]
  have l6 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l4 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l5 X1 X0 X2]
    conv => enter [1]; rw [← h53902 X0 X2 X0]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l6 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l7 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ X2)]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2 X1]
    conv => enter [1]; rw [← l11 X0 X2 X1]
  have l13 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h53902 sK0 ((sK1 ◇ sK0) ◇ X0) sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53902 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h53902 sK0 sK0 sK1]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53902 sK0 sK0 X0]
    conv => enter [1]; rw [h53902 sK0 (X0 ◇ sK0) sK1]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h53902 sK0 X0 sK1]
    conv => enter [1]; rw [l14 sK0 X0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l13 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h53902 sK0 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 X0 sK1]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h53902 sK0 (sK1 ◇ sK0) sK1]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l20 sK1 sK0 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53902 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← l17 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l23 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h53902 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1 X0]
    conv => enter [1, 2, 2]; rw [← l17 X0 sK0 sK1]
  have l24 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 1]; rw [l17 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53902 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l17 sK0 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l27 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l24 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l28 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l25 sK0 sK1]
  have l30 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1]; rw [l27 X0 sK0 sK1 X1]
  have l31 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l28 sK0 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← h53902 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0]
  have l32 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [← l17 X0 sK0 sK1]
  have l33 : ∀ sK0 sK1 X1 sK3 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X1 sK3
    conv => enter [1]; rw [l31 sK0 sK1 X1]
    conv => enter [1, 2]; rw [h53902 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK3]
  have l34 : ∀ sK0 sK1 X1 sK3 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 sK3
    conv => enter [1]; rw [l33 sK0 sK1 X1 sK3]
    conv => enter [1]; rw [← l30 X1 sK0 sK1 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l35 : ∀ X1 sK0 sK1 sK3 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1))) := by
    intro X1 sK0 sK1 sK3
    conv => enter [1]; rw [← l34 sK0 sK1 X1 sK3]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)]
  have l36 : ∀ X1 sK0 sK1 sK3 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)))) := by
    intro X1 sK0 sK1 sK3
    conv => enter [1]; rw [l35 X1 sK0 sK1 sK3]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l37 : ∀ X1 sK0 sK1 sK3 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X1))) := by
    intro X1 sK0 sK1 sK3
    conv => enter [1]; rw [l36 X1 sK0 sK1 sK3]
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK1 ◇ sK0)) sK0 X1 sK0]
  have l38 : ∀ X1 sK0 sK1 sK3 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK0 sK1 sK3
    conv => enter [1]; rw [l37 X1 sK0 sK1 sK3]
    conv => enter [1]; rw [l32 sK0 sK1 (sK0 ◇ X1)]
  have l39 : ∀ X1 sK0 sK1 sK3 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1 sK3
    conv => enter [1]; rw [l38 X1 sK0 sK1 sK3]
    conv => enter [1]; rw [← h4512 sK0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l25 sK0 sK1]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l25 sK0 sK1]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l43 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l17 sK3 sK0 sK1]
    conv => enter [1]; rw [← l40 sK3 sK0 sK1]
  have l44 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l32 sK0 sK1 X0]
    conv => enter [1]; rw [l42 sK0 sK1 X0]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h53902 sK0 (sK1 ◇ sK0) sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l47 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l48 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l47 sK1 sK0 X0]
    conv => enter [1]; rw [← l21 sK0 sK1 X0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l50 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l48 sK1 sK0 X0]
    conv => enter [1]; rw [← l44 X0 sK0 sK1]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l52 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l50 sK1 sK0 X0]
  have l53 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l39 sK1 sK0 sK1 sK3]
  have l54 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l53 sK1 sK0 sK3]
    conv => enter [1]; rw [l52 sK1 sK0 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l55 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l43 sK3 sK0 sK1]
    conv => enter [1]; rw [← l54 sK1 sK0 sK3]
  have l56 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1, 2]; rw [← l55 sK3 sK0 sK1]
  have l57 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l55 sK3 sK0 sK1]
  have l58 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [← l52 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l56 sK1 sK0 sK3]
  have l59 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [h53902 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l58 sK1 sK0 sK3]
  have l60 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [l59 sK0 sK1 sK3]
  have l61 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l55 sK3 sK0 sK1]
    conv => enter [1]; rw [l60 sK1 sK0 sK3]
  have l62 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l17 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l63 : ∀ X0 sK0 sK1 sK3 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK3
    conv => enter [1]; rw [l62 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l55 sK3 sK0 sK1]
  have l64 : ∀ sK0 sK1 X0 sK3 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0 sK3
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l57 sK0 sK1 sK3]
  have l65 : ∀ sK0 sK1 X0 sK3 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0 sK3
    conv => enter [1]; rw [l64 sK0 sK1 X0 sK3]
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l66 : ∀ X0 sK0 sK1 X1 sK3 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 sK1 X1 sK3
    conv => enter [1, 1]; rw [l63 X0 sK0 sK1 sK3]
    conv => enter [1]; rw [← h4512 X0 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1]
  have l67 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l61 sK3 sK0 sK1]
    conv => enter [1]; rw [← l63 (sK1 ◇ sK0) sK0 sK1 sK3]
  have l68 : ∀ X0 sK0 sK1 X1 sK3 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 sK1 X1 sK3
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1]; rw [l66 X0 sK0 sK1 X1 sK3]
  have l69 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l67 sK3 sK0 sK1]
    conv => enter [1]; rw [← h53902 sK0 (sK1 ◇ sK0) sK1]
  have l70 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l69 sK3 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l69 sK3 sK0 sK1]
  have l71 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l17 X0 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l72 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l69 sK3 sK0 sK1]
    conv => enter [1]; rw [← l71 X0 sK0 sK1]
  have l73 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h53902 (sK1 ◇ sK0) X0 sK0]
  have l74 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l73 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h53902 sK0 (sK1 ◇ sK0) sK1]
  have l75 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l74 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l17 X0 sK0 sK1]
  have l76 : ∀ sK0 sK1 X0 sK3 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK3
    conv => enter [1]; rw [l75 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l72 X0 sK0 sK1 sK3]
  have l77 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l76 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l63 sK0 sK0 sK1 sK0]
  have l78 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l77 sK0 sK1 X0]
  have l79 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l55 sK3 sK0 sK1]
    conv => enter [1]; rw [l78 sK1 sK0 X0]
  have l80 : ∀ X0 sK0 sK1 X1 sK3 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 sK1 X1 sK3
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l72 X0 sK0 sK1 sK3]
  have l81 : ∀ sK1 sK0 X0 X1 sK3 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1 sK3
    conv => enter [1]; rw [h53902 ((sK1 ◇ sK0) ◇ X0) X1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l79 sK3 sK0 sK1 X0]
  have l82 : ∀ sK3 sK0 sK1 X1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l79 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ X0) X1]
  have l83 : ∀ sK3 sK0 sK1 X1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l82 sK3 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l84 : ∀ sK1 sK0 X0 X1 sK3 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 sK3
    conv => enter [1]; rw [l81 sK1 sK0 X0 X1 sK3]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l85 : ∀ sK3 sK0 sK1 X1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = (sK0 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l83 sK3 sK0 sK1 X1 X0]
    conv => enter [1]; rw [l65 sK0 sK1 (X0 ◇ X1) sK3]
  have l86 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l84 sK1 sK0 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← l63 X0 sK0 sK1 sK1]
  have l87 : ∀ sK3 sK0 sK1 X1 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK1 X1 X0
    conv => enter [1]; rw [l85 sK3 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l68 sK0 sK0 sK1 (X0 ◇ X1) sK3]
  have l88 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l86 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 X0]
  have l89 : ∀ X0 X1 sK0 sK1 sK3 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 X1 sK0 sK1 sK3
    conv => enter [1]; rw [l44 (X0 ◇ X1) sK0 sK1]
    conv => enter [1]; rw [← l87 sK3 sK0 sK1 X1 X0]
  have l90 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l88 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l30 X1 sK0 sK1 X0]
  have l91 : ∀ X0 X1 sK0 sK1 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 X1 sK0 sK1 sK3
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l89 X0 X1 sK0 sK1 sK3]
  have l92 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (((sK1 ◇ sK0) ◇ X0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l80 X1 sK0 sK1 X0 sK3]
    conv => enter [1]; rw [← l90 sK1 sK0 X0 X1]
  have l93 : ∀ X0 sK3 sK0 sK1 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 sK3 sK0 sK1 X1
    conv => enter [1, 2]; rw [l72 sK3 sK0 sK1 X1]
    conv => enter [1]; rw [l91 X0 X1 sK0 sK1 sK3]
  have l94 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l92 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) X0 (((sK1 ◇ sK0) ◇ X0) ◇ X1)]
  have l95 : ∀ sK3 sK0 sK1 X1 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro sK3 sK0 sK1 X1
    conv => enter [1]; rw [l70 sK3 sK0 sK1 sK3]
    conv => enter [1]; rw [l93 sK3 sK3 sK0 sK1 X1]
  have l96 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l94 sK3 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l97 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X1))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l96 sK3 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l10 X0 (sK1 ◇ sK0) X1 (sK1 ◇ sK0)]
  have l98 : ∀ X0 X1 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro X0 X1 sK3 sK0 sK1
    conv => enter [1]; rw [← l12 X0 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [← l97 sK3 sK0 sK1 X0 X1]
  have l99 : ∀ X0 X1 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK3 sK0 sK1
    conv => enter [1]; rw [l98 X0 X1 sK3 sK0 sK1]
    conv => enter [1]; rw [← l95 sK3 sK0 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l99 x y z w x]

theorem Equation4512_53987_implies_Equation53902 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53987 : Equation53987 G) : Equation53902 G := by
  have l0 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h53987 X0 X1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ sK0)]
  have l1 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← l0 sK2 sK2 sK2 sK0]
    conv => enter [1]; rw [h53987 sK2 sK2 X1 sK0]
  have l2 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← l1 sK2 sK0 X0]
    conv => enter [1]; rw [l1 sK2 sK0 X1]
  have l3 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l2 X0 sK0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK2 ◇ sK0))]
  have l4 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [l3 X0 sK0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l2 X0 sK0 sK2 sK1]
  have l5 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X1 sK1]
  have l6 : ∀ X0 X1 X2 sK0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 X2 sK0 sK2 sK1
    conv => enter [1]; rw [h53987 X0 X1 X2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l2 X0 sK0 sK2 sK1]
  have l7 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK2 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l2 X0 sK0 sK2 sK1]
  have l8 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l6 X0 X1 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [l7 X0 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l9 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l8 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l9 x y y x z]

theorem Equation4512_53902_implies_Equation53992 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation53992 G := by
  have l0 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53902 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h53902 X0 X1 X2]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (X0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← h53902 (sK2 ◇ sK0) sK0 X0]
  have l5 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK2 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← h53902 (sK0 ◇ (sK2 ◇ sK0)) sK3 X0]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [l0 sK2 sK0 sK0]
  have l7 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l8 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2 X0]
    conv => enter [1]; rw [← l2 sK0 sK2 sK2]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l7 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l10 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h53902 sK0 sK2 sK2]
    conv => enter [1]; rw [← l8 sK0 sK2 X0]
  have l11 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l9 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l12 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l11 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l13 : ∀ sK2 sK0 X0 : G, (((sK2 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h53902 sK0 ((sK2 ◇ sK0) ◇ X0) sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53902 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h53902 sK0 sK0 sK2]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h53902 sK0 sK0 X0]
    conv => enter [1]; rw [h53902 sK0 (X0 ◇ sK0) sK2]
  have l16 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h53902 sK0 X0 sK2]
  have l17 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ ((sK0 ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l16 sK0 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK0)) X1]
  have l18 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l15 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l19 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h53902 sK0 X0 sK2]
    conv => enter [1]; rw [l14 sK0 X0 sK2]
  have l20 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l13 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) X0 (sK0 ◇ (sK2 ◇ sK0))]
  have l21 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)) = (sK0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← l17 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l22 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h53902 sK0 sK0 sK2]
    conv => enter [1]; rw [l18 sK0 X0 sK2]
  have l23 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l21 X0 sK0 sK2 X1]
    conv => enter [1]; rw [h53902 sK0 (X0 ◇ X1) sK2]
  have l24 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l23 X0 sK0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK0))]
  have l25 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h53902 sK0 (sK2 ◇ sK0) sK2]
  have l26 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [← l25 sK2 sK0 X0]
  have l27 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 1]; rw [l10 sK2 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l28 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l27 sK2 sK0 X0]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h53902 (sK0 ◇ (sK2 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← l19 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK2]
  have l30 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h53902 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l19 sK0 sK0 sK2]
  have l31 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l19 sK2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l32 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l19 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 sK2]
  have l33 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3)) = (sK3 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 sK0]
    conv => enter [1]; rw [← l32 sK3 sK0 sK2]
  have l34 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l31 sK2 sK0]
    conv => enter [1]; rw [← h53902 sK0 (sK2 ◇ sK0) sK2]
  have l35 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l29 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l10 sK2 sK0 sK0]
  have l36 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l33 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
  have l37 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l35 sK0 sK2 X0]
    conv => enter [1, 2]; rw [l34 sK2 sK0]
  have l38 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← l36 sK0 sK2 sK3]
    conv => enter [1]; rw [← l28 sK2 sK0 sK3]
  have l39 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l37 sK0 sK2 X0]
    conv => enter [1]; rw [← l19 X0 sK0 sK2]
  have l40 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l30 sK0 sK2]
  have l41 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l30 sK0 sK2]
  have l42 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l41 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l43 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l19 sK3 sK0 sK2]
    conv => enter [1]; rw [← l40 sK3 sK0 sK2]
  have l44 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l39 sK0 sK2 X0]
    conv => enter [1]; rw [l42 sK0 sK2 X0]
  have l45 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1, 2]; rw [l34 sK2 sK0]
  have l46 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l34 sK2 sK0]
  have l47 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l46 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l48 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [h53902 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l49 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l47 sK2 sK0 X0]
    conv => enter [1]; rw [← l44 X0 sK0 sK2]
  have l50 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l10 sK2 sK0 sK0]
    conv => enter [1]; rw [← l48 sK0 sK2]
  have l51 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l50 sK2 sK0]
    conv => enter [1]; rw [l34 sK2 sK0]
  have l52 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK3 sK0 sK2
    conv => enter [1, 2]; rw [← l51 sK0 sK2]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l53 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l51 sK0 sK2]
  have l54 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l53 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l55 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l19 sK3 sK0 sK2]
    conv => enter [1]; rw [l52 sK3 sK0 sK2]
  have l56 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l54 sK0 sK2 X0]
    conv => enter [1]; rw [← l44 X0 sK0 sK2]
  have l57 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l10 sK2 sK0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l55 sK3 sK0 sK2]
  have l58 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← l57 sK2 sK0 sK3]
    conv => enter [1]; rw [l34 sK2 sK0]
  have l59 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1, 2]; rw [← l58 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK2 ◇ sK0)) (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l60 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [h53902 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l58 sK0 sK2 sK3]
  have l61 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l60 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [l5 sK3 sK0 sK2 sK0]
  have l62 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l19 sK3 sK0 sK2]
    conv => enter [1]; rw [l59 sK3 sK0 sK2]
  have l63 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = (X0 ◇ (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK3))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l61 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l28 sK2 sK0 sK3]
  have l64 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l63 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l38 sK3 sK0 sK2]
  have l65 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [l24 X0 sK0 sK2 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l64 sK3 sK0 sK2 X0]
  have l66 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1, 2]; rw [← l58 sK0 sK2 sK3]
    conv => enter [1]; rw [l65 X0 sK0 sK2 sK3]
  have l67 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [l66 X0 sK0 sK2 sK3]
  have l68 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [h53902 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l62 sK3 sK0 sK2]
  have l69 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l62 sK3 sK0 sK2]
    conv => enter [1]; rw [← l68 sK3 sK0 sK2 X0]
  have l70 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [l67 X0 sK0 sK2 sK3]
    conv => enter [1]; rw [← l69 X0 sK3 sK0 sK2]
  have l71 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK3
    conv => enter [1, 2]; rw [l70 sK0 sK0 sK2 sK3]
    conv => enter [1]; rw [h53902 sK0 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK2]
  have l72 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l43 sK3 sK0 sK2]
    conv => enter [1]; rw [← l71 sK0 sK2 sK3]
  have l73 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l72 sK3 sK0 sK2]
    conv => enter [1]; rw [h53902 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l74 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h53902 (sK2 ◇ sK0) X0 sK0]
  have l75 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = (X1 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [h53902 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) X1 X0]
    conv => enter [1, 2, 2]; rw [← h53902 (sK2 ◇ sK0) X0 sK0]
  have l76 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = (X1 ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0))))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l75 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0))]
  have l77 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l74 sK0 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h53902 sK0 (sK2 ◇ sK0) sK2]
  have l78 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0)))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l76 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← l12 (sK2 ◇ sK0) X1 ((sK2 ◇ sK0) ◇ X0) (sK0 ◇ (sK2 ◇ sK0))]
  have l79 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l77 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l19 X0 sK0 sK2]
  have l80 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0)))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l78 sK2 sK0 X1 X0]
    conv => enter [1]; rw [l0 sK2 sK0 (X1 ◇ ((sK2 ◇ sK0) ◇ X0))]
  have l81 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l56 sK0 sK2 X0]
    conv => enter [1]; rw [l79 sK0 sK2 X0]
  have l82 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = ((X1 ◇ ((sK2 ◇ sK0) ◇ X0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l80 sK2 sK0 X1 X0]
    conv => enter [1]; rw [l49 sK2 sK0 (X1 ◇ ((sK2 ◇ sK0) ◇ X0))]
  have l83 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = (X1 ◇ (((sK2 ◇ sK0) ◇ X0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l82 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 ((sK2 ◇ sK0) ◇ X0) (sK0 ◇ (sK2 ◇ sK0))]
  have l84 : ∀ sK2 sK0 X1 X0 : G, (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l83 sK2 sK0 X1 X0]
    conv => enter [1]; rw [← l24 X1 sK0 sK2 ((sK2 ◇ sK0) ◇ X0)]
  have l85 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) := by
    intro X1 X0 sK0 sK2
    conv => enter [1, 2]; rw [← l56 sK0 sK2 X0]
    conv => enter [1]; rw [← l84 sK2 sK0 X1 X0]
  have l86 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l85 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)]
  have l87 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l86 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← l26 sK0 sK2 (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)]
  have l88 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l87 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← l44 (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) sK0 sK2]
  have l89 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l88 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) X1 (sK0 ◇ (sK2 ◇ sK0))]
  have l90 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l89 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l91 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l90 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← l26 sK0 sK2 (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l92 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l91 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← l44 (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 sK2]
  have l93 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l92 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
  have l94 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l93 X1 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l10 sK2 sK0 sK0]
  have l95 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l94 X1 X0 sK0 sK2]
    conv => enter [1, 2]; rw [l34 sK2 sK0]
  have l96 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l95 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← l19 X1 sK0 sK2]
  have l97 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l73 sK3 sK0 sK2]
    conv => enter [1]; rw [l30 sK0 sK2]
  have l98 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK2]
    conv => enter [1]; rw [← l22 sK0 sK2 X0]
  have l99 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l97 sK3 sK0 sK2]
    conv => enter [1]; rw [← l98 X0 sK0 sK2]
  have l100 : ∀ X0 sK0 sK2 X1 sK3 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 sK2 X1 sK3
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK2 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l99 X0 sK0 sK2 sK3]
  have l101 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 X0 sK0
    conv => enter [1, 2]; rw [l81 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l102 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK2 X0]
    conv => enter [1]; rw [← l101 sK2 X0 sK0]
  have l103 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l96 sK2 X0 sK0 sK2]
    conv => enter [1]; rw [← l102 sK0 sK2 X0]
  have l104 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l100 sK0 sK0 sK2 X0 sK3]
    conv => enter [1]; rw [← l103 sK2 sK0 X0]
  have l105 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l104 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [l34 sK2 sK0]
  have l106 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [l97 sK3 sK0 sK2]
    conv => enter [1]; rw [← l105 sK3 sK0 sK2 X0]
  have l107 : ∀ X0 X1 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [h53902 X0 X1 (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l106 sK3 sK0 sK2 X0]
  have l108 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l107 X0 X1 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l70 X0 sK0 sK2 X0]
  have l109 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l108 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l96 X1 X0 sK0 sK2]
  have l110 : ∀ X0 X1 sK3 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK3 sK0 sK2
    conv => enter [1]; rw [l109 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l99 X1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l110 x y z w y]

theorem Equation4512_53992_implies_Equation53902 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53992 : Equation53992 G) : Equation53902 G := by
  have l0 : ∀ X0 sK0 sK2 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2 X2
    conv => enter [1]; rw [← h53992 X0 sK2 X0 sK0]
    conv => enter [1]; rw [h53992 X0 sK2 X2 sK0]
  have l1 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l0 X0 sK0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK2 ◇ sK0))]
  have l2 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0 sK2 sK1]
  have l3 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK2 X1 sK1]
  have l4 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [h53992 X0 X1 X2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0 sK2 X1]
  have l5 : ∀ sK1 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1)) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X1]
  have l6 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l4 X0 X1 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l5 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l7 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l3 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l7 x y y x z]

theorem Equation4512_53902_implies_Equation54007 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53902 : Equation53902 G) : Equation54007 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53902 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h53902 sK1 sK1 sK0]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53902 sK1 sK1 X0]
    conv => enter [1]; rw [h53902 sK1 (X0 ◇ sK1) sK0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l1 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h53902 sK1 X0 sK0]
    conv => enter [1]; rw [l0 sK1 X0 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h53902 sK1 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 X0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53902 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l3 sK1 sK1 sK0]
  have l6 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK4 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l7 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l6 sK4 sK1 sK0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 X0]
  have l9 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l9 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l3 X1 sK1 sK0]
  have l11 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l7 sK4 sK1 sK0]
    conv => enter [1]; rw [l8 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 sK0]
  have l12 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l11 sK4 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK4 sK1 sK0]
  have l13 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1]; rw [l3 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l11 sK4 sK1 sK0]
  have l14 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (X0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [h53902 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 sK4]
    conv => enter [1, 2, 2]; rw [← l12 sK4 sK1 sK0 sK4]
  have l15 : ∀ sK4 sK1 sK0 X1 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK4 sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) X1]
  have l16 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l14 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [← l15 sK4 sK1 sK0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l17 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l13 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 sK0 sK4]
    conv => enter [1]; rw [← l16 sK4 sK1 sK0 X0]
  have l18 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l15 sK4 sK1 sK0 X0 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l17 sK4 sK1 sK0 X0]
  have l19 : ∀ sK4 sK1 sK0 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [l7 sK4 sK1 sK0]
    conv => enter [1]; rw [← l18 sK4 sK1 sK0 X0]
  have l20 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h53902 X0 X1 (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l19 sK4 sK1 sK0 X0]
  have l21 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l20 X0 X1 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l13 X0 sK1 sK0 X0]
  have l22 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 X1 X0]
  have l23 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK4 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← l11 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l23 x y z w u]

@[equational_result]
theorem Equation54007_implies_Equation53902 (G : Type*) [Magma G] (h54007 : Equation54007 G) : Equation53902 G := by
  intro x y z
  conv => enter [1]; rw [h54007 x y y x z]

theorem Equation4512_53903_implies_Equation53929 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53903 : Equation53903 G) : Equation53929 G := by
  have l0 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  have l1 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK3 ◇ (sK0 ◇ sK2)) X0]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK3 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h53903 X1 (X2 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h53903 X0 X1 X2]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) = ((X0 ◇ (X0 ◇ X1)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h53903 X0 X1 X2]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ sK2)) (X0 ◇ sK2)]
    conv => enter [1]; rw [← h53903 (sK3 ◇ (sK0 ◇ sK2)) sK2 X0]
  have l7 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h53903 X0 (sK1 ◇ sK2) X1]
  have l8 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) = (X0 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X2 X1 (X0 ◇ (X0 ◇ X1))]
  have l10 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l8 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h53903 X0 X1 X0]
    conv => enter [1]; rw [← l9 X1 X2 X0]
  have l12 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l10 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X1) X3]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1]; rw [← h53903 X1 X1 X2]
  have l14 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l12 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l15 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)) = (sK2 ◇ (sK2 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ sK2)) ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)]
    conv => enter [1, 2]; rw [h53903 (sK3 ◇ (sK0 ◇ sK2)) sK2 sK0]
  have l16 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1, 2]; rw [h53903 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK0 ◇ sK2))]
  have l17 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [h53903 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ (sK0 ◇ sK2))]
  have l18 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) = ((X0 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ sK2)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [h53903 X1 (X0 ◇ (sK0 ◇ sK2)) sK2]
    conv => enter [1, 2, 2]; rw [← h53903 X0 sK2 sK0]
  have l19 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) = (X0 ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ (X0 ◇ (X0 ◇ sK2))))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l18 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK2) (X1 ◇ (X0 ◇ (X0 ◇ sK2)))]
  have l20 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l13 sK0 X0 sK2]
    conv => enter [1]; rw [l17 sK0 X0 sK2]
  have l21 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [← l13 sK1 X0 sK2]
    conv => enter [1]; rw [l16 sK1 X0 sK2 sK0]
  have l22 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l15 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
  have l23 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ (X0 ◇ sK2)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l19 X1 X0 sK0 sK2]
    conv => enter [1]; rw [← l14 (sK0 ◇ sK2) X0 (X0 ◇ sK2) X1]
  have l24 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← l6 sK2 sK3 sK0 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l22 sK2 sK3 sK0]
  have l25 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l23 X1 X0 sK0 sK2]
    conv => enter [1, 2]; rw [l13 (sK0 ◇ sK2) X0 sK2]
  have l26 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l24 sK3 sK0 sK2]
    conv => enter [1]; rw [h53903 (sK3 ◇ (sK0 ◇ sK2)) sK2 sK1]
  have l27 : ∀ sK2 X1 X0 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X1 X0 sK0
    conv => enter [1]; rw [← l13 (sK0 ◇ sK2) sK2 sK2]
    conv => enter [1]; rw [← l25 X1 X0 sK0 sK2]
  have l28 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l26 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK2)]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h53903 sK1 sK2 sK0]
  have l30 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53903 sK2 (sK0 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h53903 sK1 sK2 sK0]
  have l31 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53903 sK2 sK2 sK0]
    conv => enter [1]; rw [l30 sK2 sK0 sK1]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l21 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 sK2]
  have l33 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l28 sK2 sK3 sK0 sK1]
  have l34 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [h53903 sK2 (sK0 ◇ sK2) (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [l28 sK2 sK3 sK0 sK1]
  have l35 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)))) = (((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h53903 X0 ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) sK2]
    conv => enter [1, 2, 2]; rw [l28 sK2 sK3 sK0 sK1]
  have l36 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l35 X0 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2) (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)))]
  have l37 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [h53903 sK2 sK2 sK0]
    conv => enter [1]; rw [l34 sK2 sK0 sK3 sK1]
  have l38 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l33 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [l1 sK0 sK2 sK3 (sK1 ◇ sK2)]
  have l39 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l36 X0 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l14 (sK0 ◇ sK2) (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) (sK1 ◇ sK2) X0]
  have l40 : ∀ sK0 sK2 sK1 sK3 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [← l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l37 sK2 sK0 sK3 sK1]
  have l41 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [l20 sK2 sK0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [l38 sK0 sK2 sK3 sK1]
  have l42 : ∀ sK2 sK0 sK3 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK3 sK1
    conv => enter [1]; rw [l27 sK2 sK2 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1]; rw [l39 sK2 sK2 sK3 sK0 sK1]
  have l43 : ∀ sK0 sK2 sK1 sK3 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [← l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l41 sK2 sK0 sK3 sK1]
  have l44 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l42 sK2 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l40 sK0 sK2 sK1 sK2]
  have l45 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l44 sK2 sK0 sK1]
  have l46 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l31 sK2 sK0 sK1]
  have l47 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l31 sK2 sK0 sK1]
    conv => enter [1]; rw [h53903 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [l31 sK2 sK0 sK1]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l32 sK2 sK1]
    conv => enter [1]; rw [l31 sK2 sK0 sK1]
  have l49 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l48 sK1 sK2 sK0]
  have l50 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (sK3 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l43 sK0 sK2 sK1 sK3]
  have l51 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l50 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l52 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l51 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [h53903 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK2) sK1]
  have l53 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l52 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l54 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l47 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l55 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l47 sK0 sK2 sK1]
  have l56 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l46 sK0 sK2 sK1]
    conv => enter [1]; rw [← l55 sK0 sK2 sK1]
  have l57 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l48 sK1 sK2 sK1]
    conv => enter [1]; rw [l54 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [← l48 sK1 sK2 sK1]
  have l58 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l56 sK0 sK2 sK1]
    conv => enter [1]; rw [← l45 sK0 sK2 sK1]
  have l59 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53903 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l57 sK1 sK2]
  have l60 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l58 sK0 sK2 sK1]
    conv => enter [1]; rw [← l48 sK1 sK2 sK0]
  have l61 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h53903 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK1 ◇ sK2))]
  have l62 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1, 2]; rw [h53903 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ (sK1 ◇ sK2))]
  have l63 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [← l13 sK0 X0 sK2]
    conv => enter [1]; rw [l62 sK0 X0 sK2 sK1]
  have l64 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l13 sK1 X0 sK2]
    conv => enter [1]; rw [l61 sK1 X0 sK2]
  have l65 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l63 sK2 sK0 X0 sK1]
  have l66 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l64 sK2 sK1 X0]
  have l67 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [l65 sK0 sK2 sK1 X0]
  have l68 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK1]
    conv => enter [1]; rw [l66 sK1 sK2 sK1 X0]
  have l69 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h53903 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l70 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53903 X0 (sK1 ◇ (sK1 ◇ sK2)) sK2]
    conv => enter [1, 2, 2]; rw [← h53903 sK1 sK2 sK1]
  have l71 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h53903 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l72 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l69 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l73 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l59 sK1 sK2]
    conv => enter [1]; rw [l72 sK1 sK2]
  have l74 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l73 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l75 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l74 sK1 sK2 X0]
  have l76 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l67 sK1 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l77 : ∀ sK3 sK0 sK2 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l67 sK1 sK2 sK0 X0]
  have l78 : ∀ sK3 sK0 sK2 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0 sK1
    conv => enter [1]; rw [l77 sK3 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [← l49 sK3 sK0 sK2 sK1]
  have l79 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53903 X0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l71 sK1 sK2 (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h53903 X0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l80 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53903 (sK1 ◇ (sK1 ◇ sK2)) sK2 X0]
    conv => enter [1]; rw [← l71 sK1 sK2 (X0 ◇ sK2)]
  have l81 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l80 sK1 sK2 X0]
    conv => enter [1]; rw [← l75 sK1 sK2 sK2]
  have l82 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l79 X0 sK1 sK2]
    conv => enter [1]; rw [l13 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
  have l83 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l82 X0 sK1 sK2]
    conv => enter [1]; rw [← l75 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l84 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l83 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l73 sK1 sK2]
  have l85 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l59 sK1 sK2]
    conv => enter [1]; rw [← l84 X0 sK1 sK2]
  have l86 : ∀ sK2 sK3 sK0 X0 sK1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ (sK0 ◇ sK2)) (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l78 sK3 sK0 sK2 X0 sK1]
  have l87 : ∀ sK2 sK3 sK0 X0 sK1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l86 sK2 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l88 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h53903 sK1 (sK1 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l53 sK3 sK0 sK2 sK1]
  have l89 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l59 sK1 sK2]
    conv => enter [1]; rw [l88 sK1 sK2 sK3 sK0]
  have l90 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l85 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [← h53903 sK1 sK2 sK1]
  have l91 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l85 sK1 sK2 X0]
    conv => enter [1]; rw [h53903 X0 (sK1 ◇ (sK1 ◇ sK2)) X1]
  have l92 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53903 X0 (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
    conv => enter [1, 2, 2]; rw [← l85 sK1 sK2 X1]
  have l93 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l92 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← h4512 X1 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l94 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53903 sK1 sK2 sK1]
    conv => enter [1]; rw [← l90 sK1 sK2]
  have l95 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l91 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l93 X0 X1 sK1 sK2]
  have l96 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [l95 X1 sK1 sK2 X0]
  have l97 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l98 : ∀ sK0 sK2 sK3 X0 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK3 X0 sK1
    conv => enter [1]; rw [← l1 sK0 sK2 sK3 (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l87 sK2 sK3 sK0 X0 sK1]
  have l99 : ∀ sK0 sK2 sK3 X0 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK3 X0 sK1
    conv => enter [1]; rw [l98 sK0 sK2 sK3 X0 sK1]
    conv => enter [1]; rw [l1 sK0 sK2 sK3 (sK1 ◇ (sK1 ◇ sK2))]
  have l100 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l76 sK1 sK2 sK0 (sK3 ◇ (sK0 ◇ sK2)) sK1]
  have l101 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [l100 sK1 sK2 sK0 sK3]
  have l102 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l101 sK1 sK2 sK0 sK3]
  have l103 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l70 (sK3 ◇ (sK0 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [l102 sK3 sK0 sK2 sK1]
  have l104 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l89 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l103 sK1 sK2 sK3 sK1]
  have l105 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [l104 sK1 sK2 sK3]
  have l106 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l49 sK3 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l94 sK1 sK2]
  have l107 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l105 sK1 sK2 sK3]
    conv => enter [1]; rw [← l106 sK3 sK0 sK2 sK1]
  have l108 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l60 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK2) (sK2 ◇ sK2)]
  have l109 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l49 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l108 sK3 sK1 sK2 sK0]
  have l110 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l107 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l109 sK3 sK0 sK2 sK1]
  have l111 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l110 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 (sK2 ◇ sK2)]
  have l112 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [← l6 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← l111 sK1 sK2 sK3 sK0]
  have l113 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l112 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l69 sK1 sK2]
  have l114 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [← l113 sK1 sK3 sK0 sK2]
  have l115 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l114 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l116 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h53903 X1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← h53903 X0 (sK1 ◇ sK2) sK1]
  have l117 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l116 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK2)) (X1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2))))]
  have l118 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l117 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l14 (sK1 ◇ (sK1 ◇ sK2)) X0 (X0 ◇ (sK1 ◇ sK2)) X1]
  have l119 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l118 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l75 sK1 sK2 (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))]
  have l120 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l97 sK1 sK2 (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l119 X1 X0 sK1 sK2]
  have l121 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l96 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l120 sK1 sK2 X0 X0]
  have l122 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l121 X0 sK1 sK2]
    conv => enter [1]; rw [l7 sK1 sK2 X0 X0]
  have l123 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l122 X0 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 X0 (sK1 ◇ sK2)]
  have l124 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l123 X0 sK1 sK2]
    conv => enter [1]; rw [← l68 sK1 sK2 (sK1 ◇ sK2)]
  have l125 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [← l124 X0 sK1 sK2]
  have l126 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l115 sK1 sK2]
  have l127 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [← l126 sK1 sK2]
  have l128 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l127 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK2 ◇ sK2)]
  have l129 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l128 sK1 sK2]
    conv => enter [1]; rw [l81 sK1 sK2 sK2]
  have l130 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l129 sK1 sK2]
    conv => enter [1]; rw [← l97 sK1 sK2 sK2]
  have l131 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l94 sK1 sK2]
    conv => enter [1]; rw [l130 sK1 sK2]
  have l132 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53903 X0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l131 sK1 sK2]
  have l133 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l132 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l125 sK1 sK2 X0]
  have l134 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53903 sK1 sK2 sK1]
    conv => enter [1]; rw [← l133 X0 sK2 sK1]
  have l135 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l134 sK1 sK2 X0]
    conv => enter [1]; rw [h53903 X0 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l135 x y z w]

@[equational_result]
theorem Equation53929_implies_Equation53903 (G : Type*) [Magma G] (h53929 : Equation53929 G) : Equation53903 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h53929 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [h53929 sK1 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53929 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

end Semigroup5
