import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54119_implies_Equation54059 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54119 : Equation54119 G) : Equation54059 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54119 (sK0 ◇ sK1) sK2 X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54119 X2 X1 X1]
    conv => enter [1, 2]; rw [h54119 X1 X2 X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← h54119 (sK1 ◇ sK2) X0 sK0]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54119 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54119 sK2 X0 (sK0 ◇ sK1)]
  have l7 : ∀ X1 sK1 sK2 X0 sK0 : G, (X1 ◇ (X1 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0))) = (((sK1 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X1 sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h54119 ((sK1 ◇ sK2) ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l8 : ∀ X1 sK1 sK2 X0 sK0 : G, (X1 ◇ (X1 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ sK0))) = ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X1 sK1 sK2 X0 sK0
    conv => enter [1]; rw [l7 X1 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l11 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54119 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h54119 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
  have l13 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h54119 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54119 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l15 : ∀ sK1 sK2 X0 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = (X1 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1]; rw [← l8 X1 sK1 sK2 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK2) X0 sK0]
  have l16 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK1 ◇ sK2) ◇ ((X0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l15 sK1 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ sK2) (X0 ◇ sK0) sK1]
  have l17 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l16 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 (X0 ◇ sK0)]
  have l18 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l12 sK2 sK1 sK2]
  have l19 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK2) sK0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l19 sK1 sK2 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 sK2]
  have l21 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l12 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK1 sK2 sK0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2) X0]
  have l24 : ∀ sK1 sK2 X0 sK0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)))) := by
    intro sK1 sK2 X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l3 ((sK1 ◇ sK2) ◇ X0) sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK2) X0]
  have l25 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l12 sK2 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l13 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 (sK1 ◇ sK2) sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK1 sK0 sK1 sK2]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK1 sK0 sK1]
  have l29 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l24 sK1 sK2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h54119 (sK0 ◇ (sK1 ◇ sK2)) X0 sK1]
  have l30 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK2) sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l9 sK0 sK1 sK2 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l27 sK1 sK2 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 sK1]
  have l34 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l29 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l35 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l38 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1]; rw [l34 sK1 sK2 X0 sK0]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l17 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l38 sK1 sK2 X0 sK0]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l37 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 (sK0 ◇ sK1) sK1 sK0]
    conv => enter [1, 2]; rw [← l37 sK1 sK0]
  have l42 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [l3 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l37 sK1 sK0]
  have l43 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK1 sK0]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l41 sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0 sK1]
    conv => enter [1]; rw [← l44 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [l47 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1]
    conv => enter [1, 2]; rw [l32 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l14 sK1 sK0 sK1]
  have l55 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 sK2]
  have l56 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l12 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l35 sK2 sK1 sK0]
  have l57 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l58 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l36 sK0 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [l58 sK1 sK2 sK0]
  have l60 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l55 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK2 sK0]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l60 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l62 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l62 sK1 sK0 sK2]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l64 y x z]

theorem Equation4512_54059_implies_Equation54119 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54059 : Equation54059 G) : Equation54119 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54059 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 sK2 X0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK2 X0]
  have l3 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK2 ◇ (((sK2 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK2 ◇ sK1) ◇ X0) X1]
  have l4 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l3 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) X0 X1]
  have l5 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l4 sK1 sK2 X1 sK1]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h54059 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 X0]
  have l8 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h54059 X1 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK2 X1]
  have l9 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l8 X1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 X0]
  have l10 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l9 X1 X0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 X0]
  have l11 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [← h54059 X1 X0 X2]
    conv => enter [1]; rw [l10 X1 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l11 z x y x y]

theorem Equation4512_54119_implies_Equation54121 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54119 : Equation54119 G) : Equation54121 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ sK2)) = (X1 ◇ (X1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h54119 sK2 ((sK0 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK0 ◇ sK2) X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54119 X2 X1 X1]
    conv => enter [1, 2]; rw [h54119 X1 X2 X0]
  have l4 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h54119 sK2 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54119 (sK0 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK2) X0]
  have l6 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (X1 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ sK2))) = (((sK0 ◇ sK2) ◇ X0) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [← h54119 ((sK0 ◇ sK2) ◇ X0) sK2 X1]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK2) X0]
  have l7 : ∀ X1 sK0 sK2 X0 : G, (X1 ◇ (X1 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro X1 sK0 sK2 X0
    conv => enter [1]; rw [l6 X1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) X0 ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)]
  have l8 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK0 X0 sK2]
    conv => enter [1]; rw [← h54119 (sK2 ◇ (sK0 ◇ sK2)) X0 sK2]
  have l9 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54119 sK2 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) sK2]
  have l10 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h54119 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 sK2]
  have l11 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h54119 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK2 sK0]
  have l12 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0))) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← l7 X1 sK0 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK2) X0 sK2]
  have l13 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l8 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 sK2]
  have l14 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0))) = ((sK0 ◇ sK2) ◇ ((X0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l12 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← h54119 (sK0 ◇ sK2) (X0 ◇ sK2) sK0]
  have l15 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l13 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) (X0 ◇ sK2)]
  have l16 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l14 sK0 sK2 X0]
    conv => enter [1]; rw [l5 sK0 sK2 (X0 ◇ sK2)]
  have l17 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [← l9 (sK0 ◇ sK2) sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l18 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1]; rw [l15 sK2 sK0 (sK0 ◇ sK2)]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l11 sK2 sK0 sK2]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [← l11 (sK2 ◇ (sK0 ◇ sK2)) sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1]; rw [l16 sK0 sK2 (sK0 ◇ sK2)]
  have l22 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 sK2 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1, 2]; rw [← l18 sK2 sK0]
  have l24 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l22 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK2 sK2]
  have l25 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h54119 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK2]
    conv => enter [1]; rw [← l23 sK0 sK2]
  have l26 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 sK2 sK0 sK0]
    conv => enter [1]; rw [← l25 sK2 sK0]
  have l27 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l26 sK2 sK0]
    conv => enter [1]; rw [l15 sK2 sK0 sK2]
  have l28 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l24 sK2 sK0]
    conv => enter [1]; rw [← h54119 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK2]
  have l29 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l28 sK2 sK0]
    conv => enter [1]; rw [l15 sK2 sK0 sK2]
  have l30 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l27 sK2 sK0]
    conv => enter [1]; rw [← l29 sK2 sK0]
  have l31 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1, 2, 2]; rw [l30 sK2 sK0]
    conv => enter [1]; rw [← h54119 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l32 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l24 sK2 sK0]
    conv => enter [1]; rw [← l31 X0 sK2 sK0]
  have l33 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1) = (X0 ◇ ((X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1)) := by
    intro sK2 sK0 X1 X0
    conv => enter [1, 1]; rw [l32 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X1]
  have l34 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l33 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ (sK0 ◇ sK2)) X1]
  have l35 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X1) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l34 sK2 sK0 X1 sK2]
    conv => enter [1]; rw [← h54119 (sK2 ◇ (sK0 ◇ sK2)) X1 sK2]
  have l36 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK2 sK0
    conv => enter [1, 2, 2]; rw [l32 sK2 sK0 X0]
    conv => enter [1]; rw [← l3 (sK2 ◇ (sK0 ◇ sK2)) X0 X0]
  have l37 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l35 sK2 sK0 X0]
    conv => enter [1]; rw [← l36 X0 sK2 sK0]
  have l38 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l32 sK2 sK0 X0]
    conv => enter [1]; rw [← l37 sK2 sK0 X0]
  have l39 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [l38 sK2 sK0 ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [l10 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK3]
  have l40 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [← l39 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l40 z x w y]

theorem Equation4512_54121_implies_Equation54119 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54121 : Equation54121 G) : Equation54119 G := by
  have l0 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h54121 sK0 (sK1 ◇ sK2) X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h54121 sK0 (sK1 ◇ sK2) sK0 (sK1 ◇ sK2)]
  have l2 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ X1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [← h54121 sK0 X0 X0 X1]
    conv => enter [1]; rw [h54121 sK0 X0 sK0 (sK1 ◇ sK2)]
  have l3 : ∀ X1 X2 X0 sK0 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro X1 X2 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54121 X1 X2 X0 (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0 sK1 sK2]
  have l4 : ∀ X1 X2 X0 sK0 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 X2 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l3 X1 X2 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 sK2]
  have l5 : ∀ X1 X2 sK0 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X1 X2 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 X1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l7 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK2 sK0 sK1 sK2]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54121 sK1 sK0 sK0 sK2]
    conv => enter [1]; rw [l5 sK1 sK0 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l12 z x y]

theorem Equation4512_54119_implies_Equation54066 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54119 : Equation54119 G) : Equation54066 G := by
  have l0 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h54119 sK1 ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l1 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ ((sK3 ◇ X0) ◇ sK2)) = (X1 ◇ (X1 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h54119 sK2 (sK3 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK3 X0]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54119 X2 X1 X1]
    conv => enter [1, 2]; rw [h54119 X1 X2 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54119 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) X0 sK1]
  have l5 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h54119 (sK1 ◇ (sK2 ◇ sK3)) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54119 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l7 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ sK3)) = (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [h54119 sK3 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK3 X0]
  have l8 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X0]
  have l9 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ X0) ◇ sK2)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l1 sK2 sK3 X0 sK2]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) X0 sK2]
  have l10 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h54119 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 sK2]
  have l11 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← h54119 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l12 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← h54119 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) sK1]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54119 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l14 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 X0 sK1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0 sK1]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54119 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l16 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK2 ◇ ((sK3 ◇ X0) ◇ sK2)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← l9 sK2 sK3 X0]
  have l17 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) X0 sK1]
  have l18 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK2 ◇ (sK3 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l16 sK1 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 sK3 X0 sK2]
  have l19 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l17 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ sK1)]
  have l20 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l18 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 (X0 ◇ sK2)]
  have l21 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK3 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [l10 sK3 sK2 sK3]
  have l22 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l21 sK2 sK3]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK3]
  have l23 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2, 2]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) sK2 X0]
  have l24 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l23 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK2]
  have l25 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l11 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l24 sK1 sK1 sK2 sK3]
  have l26 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1)) = (((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) ◇ X1) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) X1]
    conv => enter [1, 1]; rw [l12 X0 sK1 sK2 sK3]
  have l27 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ X1)) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [l26 X0 sK1 sK2 sK3 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) sK1 X1]
  have l28 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X1))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ X1)) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK1 ◇ (sK2 ◇ sK3)) X1]
    conv => enter [1]; rw [l27 X0 sK1 sK2 sK3 X1]
  have l29 : ∀ sK1 sK2 sK3 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [h54119 (sK1 ◇ (sK2 ◇ sK3)) X1 sK1]
    conv => enter [1]; rw [l28 sK1 sK1 sK2 sK3 X1]
  have l30 : ∀ sK1 sK2 sK3 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1)) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [← l29 sK1 sK2 sK3 X1]
    conv => enter [1]; rw [l5 sK1 sK2 sK3 X1]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l31 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l33 sK1 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l34 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
    conv => enter [1, 1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l40 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1]
    conv => enter [1, 1]; rw [l15 X0 sK0 sK1]
  have l41 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l40 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X1]
  have l42 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l41 X0 sK0 sK1 X1]
    conv => enter [1]; rw [l39 sK0 sK1 X1]
  have l43 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l42 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l44 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l43 sK0 sK1 X1 sK0]
    conv => enter [1]; rw [← h54119 (sK0 ◇ (sK1 ◇ sK0)) X1 sK0]
  have l45 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ X0)) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [h54119 X0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK3 X0]
  have l46 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l10 (sK2 ◇ sK3) sK2 sK3]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 (sK2 ◇ sK3)]
  have l47 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [l46 sK2 sK3 sK1]
  have l48 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l8 sK1 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l47 sK1 sK2 sK3]
  have l49 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l10 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2 sK3]
    conv => enter [1, 2]; rw [← l47 sK1 sK2 sK3]
  have l50 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [l49 sK2 sK3 sK1]
  have l51 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l11 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l50 sK1 sK2 sK3]
  have l52 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l50 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l53 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l51 sK1 sK2 sK3]
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
  have l54 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l53 sK1 sK2 sK3]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK1]
  have l55 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 X0]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK2 sK3 sK1]
  have l56 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ X0)) = (((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 X0]
    conv => enter [1, 1]; rw [l8 sK1 sK2 sK3 sK1]
  have l57 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ X0)) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l56 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l58 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l55 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l59 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l58 sK1 sK2 sK3]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 (sK1 ◇ (sK2 ◇ sK3))]
  have l60 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l19 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l59 sK1 sK2 sK3]
  have l61 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l60 sK1 sK2 sK3]
    conv => enter [1]; rw [l57 sK1 sK2 sK3 sK1]
  have l62 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l61 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l12 sK1 sK1 sK2 sK3]
  have l63 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l50 sK1 sK2 sK3]
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
  have l64 : ∀ X0 sK2 sK3 X1 : G, ((X0 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ sK2)) = (X0 ◇ (X1 ◇ (X1 ◇ ((sK2 ◇ sK3) ◇ sK2)))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1, 2]; rw [← l10 X0 sK2 sK3]
    conv => enter [1]; rw [l2 (X0 ◇ (sK2 ◇ sK3)) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l10 X0 sK2 sK3]
  have l65 : ∀ sK2 sK1 sK3 X0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK2 sK1 sK3 X0
    conv => enter [1, 2]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ sK3) X0]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK1 sK2 sK3]
  have l66 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [l63 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK2 ◇ sK3) X0]
    conv => enter [1, 2, 2, 2]; rw [← l63 sK1 sK2 sK3]
  have l67 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK2 ◇ sK3)) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l68 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l67 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [l30 sK1 sK2 sK3 ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)]
  have l69 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l66 sK1 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK1 sK2 sK3]
  have l70 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [l65 sK2 sK1 sK3 sK2]
    conv => enter [1, 2]; rw [l11 sK2 sK1 sK2 sK3]
  have l71 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ sK3)) = (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l2 sK3 sK2 sK3]
    conv => enter [1, 2]; rw [l10 sK3 sK2 sK3]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK0]
  have l73 : ∀ X0 sK2 sK3 : G, ((X0 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l64 X0 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h54119 (sK2 ◇ sK3) sK2 X0]
  have l74 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [l52 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← l68 X0 sK1 sK2 sK3]
  have l75 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l45 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l69 sK1 sK2 sK3]
  have l76 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l45 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l70 sK2 sK1 sK3]
  have l77 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [l71 sK3 sK2]
    conv => enter [1]; rw [l22 sK2 sK3 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK0]
  have l79 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK3 sK2]
    conv => enter [1]; rw [← l73 X0 sK2 sK3]
  have l80 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l75 sK1 sK2 sK3]
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
  have l81 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) sK1]
    conv => enter [1]; rw [l76 sK1 sK2 sK3]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l83 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ sK2))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l79 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ sK2)]
  have l84 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ sK1)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l80 sK1 sK2 sK3]
    conv => enter [1]; rw [l54 sK2 sK3 sK1]
  have l85 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l12 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l81 sK1 sK2 sK3]
  have l86 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l83 X0 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l20 sK1 sK2 sK3 (sK2 ◇ sK3)]
  have l87 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) sK1]
    conv => enter [1]; rw [l84 sK1 sK2 sK3]
  have l88 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l47 sK1 sK2 sK3]
    conv => enter [1]; rw [← l86 X0 sK1 sK2 sK3]
  have l89 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l12 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l87 sK1 sK2 sK3]
  have l90 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l88 X0 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l25 sK1 sK2 sK3]
  have l91 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l90 X0 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK3 sK1]
  have l92 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l91 X0 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l89 sK1 sK2 sK3]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [← l82 sK0 sK1]
  have l95 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l82 sK0 sK1]
  have l96 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l97 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l95 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l15 sK0 sK0 sK1]
  have l98 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← l94 sK0 sK1]
  have l99 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l96 sK0 sK1 sK0]
    conv => enter [1]; rw [← l97 sK0 sK1]
  have l100 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l99 sK0 sK1]
    conv => enter [1]; rw [← l93 sK0 sK1]
  have l101 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1]
    conv => enter [1]; rw [l100 sK0 sK1]
  have l102 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l98 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l103 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l104 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [← h54119 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l105 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l104 X0 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l106 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← l103 sK1 sK0]
  have l107 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l105 X0 sK0 sK1]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l108 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← l107 X0 sK0 sK1]
  have l109 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l102 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l110 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK3 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l10 sK3 sK2 sK3]
    conv => enter [1, 2]; rw [l77 sK3 sK2 sK1]
  have l111 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l110 sK2 sK3 sK1]
    conv => enter [1]; rw [l7 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2]
  have l112 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l111 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l54 sK2 sK3 sK1]
  have l113 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l112 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [← l89 sK1 sK2 sK3]
  have l114 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l113 sK2 sK3 sK1]
    conv => enter [1]; rw [← l92 sK2 sK1 sK2 sK3]
  have l115 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l114 sK2 sK3 sK1]
    conv => enter [1]; rw [← l85 sK1 sK2 sK3]
  have l116 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [l115 sK2 sK3 sK1]
  have l117 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [l116 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l116 sK1 sK2 sK3]
  have l118 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1, 2]; rw [← l11 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [← l117 sK1 sK2 sK3 sK1]
  have l119 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l118 sK1 sK2 sK3]
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
  have l120 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l119 sK1 sK2 sK3]
    conv => enter [1]; rw [l54 sK2 sK3 sK1]
  have l121 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l89 sK1 sK2 sK3]
    conv => enter [1]; rw [← l120 sK1 sK2 sK3]
  have l122 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l74 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l121 sK1 sK2 sK3]
  have l123 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l116 sK1 sK2 sK3]
    conv => enter [1]; rw [← l122 sK1 sK2 sK3]
  have l124 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l123 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l125 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l124 sK1 sK2 sK3]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK1]
  have l126 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2, 2]; rw [l124 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 X0]
  have l127 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l126 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK1]
  have l128 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ sK1)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l127 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [l57 sK1 sK2 sK3 sK1]
  have l129 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l128 X0 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l12 sK1 sK1 sK2 sK3]
  have l130 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l129 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l62 sK1 sK2 sK3]
  have l131 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l11 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l130 sK1 sK1 sK2 sK3]
  have l132 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l8 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l131 sK1 sK2 sK3]
  have l133 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l89 sK1 sK2 sK3]
    conv => enter [1]; rw [l132 sK2 sK3 sK1]
  have l134 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l116 sK1 sK2 sK3]
    conv => enter [1]; rw [l133 sK1 sK2 sK3]
  have l135 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l125 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l136 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l134 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l137 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1, 2]; rw [l108 sK0 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l138 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1, 2]; rw [l108 sK0 sK1 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l139 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l138 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l136 sK1 sK2 sK3 (sK0 ◇ (sK1 ◇ sK0))]
  have l140 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1]; rw [l137 sK1 sK0 sK2 sK3]
  have l141 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1]; rw [l139 sK1 sK0 sK2 sK3]
  have l142 : ∀ sK0 sK1 sK2 sK3 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK3) ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l2 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK3) (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2, 2]; rw [← l140 sK0 sK1 sK2 sK3]
  have l143 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l135 sK1 sK2 sK3 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l142 sK0 sK1 sK2 sK3]
  have l144 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l143 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l44 sK0 sK1 (sK2 ◇ sK3)]
  have l145 : ∀ sK0 sK1 sK2 sK3 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l109 sK0 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l144 sK1 sK2 sK3 sK0]
  have l146 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l141 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l145 sK0 sK1 sK2 sK3]
  have l147 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l10 (sK0 ◇ (sK1 ◇ sK0)) sK2 sK3]
    conv => enter [1, 2]; rw [← l146 sK0 sK1 sK2 sK3]
  have l148 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l147 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l93 sK0 sK1]
  have l149 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [l101 sK0 sK1]
    conv => enter [1]; rw [← l148 sK2 sK3 sK0 sK1]
  have l150 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [← l149 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [← l150 y z w x]

theorem Equation4512_54066_implies_Equation54119 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54066 : Equation54066 G) : Equation54119 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l5 sK1 sK2]
  have l7 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [h54066 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0 sK0 (sK1 ◇ sK2)]
  have l9 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← h54066 X0 X0 X1 X2]
    conv => enter [1]; rw [h54066 X0 X0 sK0 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h54066 (sK1 ◇ sK2) sK1 sK0 (sK1 ◇ sK2)]
  have l11 : ∀ X1 sK0 sK1 sK2 X2 X0 : G, (X1 ◇ ((X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 sK0 sK1 sK2 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X2]
    conv => enter [1, 1]; rw [← h54066 X0 X1 sK0 (sK1 ◇ sK2)]
  have l12 : ∀ X1 sK0 sK1 sK2 X2 X0 : G, (X1 ◇ ((X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 sK0 sK1 sK2 X2 X0
    conv => enter [1]; rw [l11 X1 sK0 sK1 sK2 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l13 : ∀ X1 sK0 sK1 sK2 X2 X0 : G, (X1 ◇ ((X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 sK0 sK1 sK2 X2 X0
    conv => enter [1]; rw [l12 X1 sK0 sK1 sK2 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l15 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X2))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← l13 X1 sK0 sK1 sK2 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ (sK1 ◇ sK2)) X2]
  have l16 : ∀ X1 sK0 sK1 sK2 X0 X2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 sK0 sK1 sK2 X0 X2
    conv => enter [1]; rw [← l9 X1 (sK0 ◇ (sK1 ◇ sK2)) X2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [h54066 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0 (sK1 ◇ sK2)]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [h54066 (sK1 ◇ sK2) sK0 sK0 (sK1 ◇ sK2)]
  have l19 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h54066 sK2 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h54066 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54066 sK2 sK1 sK0 (sK1 ◇ sK2)]
  have l20 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 1]; rw [h54066 sK2 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l21 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l20 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l22 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l19 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK2))]
  have l23 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l21 sK2 sK1 X0 sK0]
    conv => enter [1]; rw [l9 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0 sK1 sK2]
  have l24 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l23 sK2 sK1 X0 sK2]
    conv => enter [1]; rw [← l10 sK1 sK2 sK2]
  have l25 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l24 sK2 sK1 X0]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [h54066 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [h54066 sK2 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h54066 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h54066 (sK1 ◇ sK2) sK1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l29 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [h54066 X0 (sK2 ◇ sK1) sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l3 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l30 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l29 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l7 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l31 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l27 sK1 sK0 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l25 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1]; rw [← l30 sK2 sK1 X0 sK1]
  have l34 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK1 ◇ sK2))]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1)]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l36 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l16 X0 sK0 sK1 sK2 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l33 sK1 sK2 X0]
  have l37 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l22 sK2 sK1 sK2]
    conv => enter [1]; rw [← l34 sK1 sK2 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l39 sK0 sK1 sK2 X0]
  have l41 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h54066 X0 sK0 sK0 (sK1 ◇ sK2)]
  have l42 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK0 X1 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l43 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l42 X0 sK0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l44 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l16 sK0 sK0 sK1 sK2 sK0 X1]
    conv => enter [1]; rw [← l43 sK0 sK1 sK2 X1 sK0]
  have l45 : ∀ sK1 sK2 sK0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [← l36 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l44 sK0 sK1 sK2 X1]
  have l46 : ∀ sK2 sK1 sK0 X1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK2 sK1 sK0 X1
    conv => enter [1]; rw [l37 sK2 sK1]
    conv => enter [1]; rw [l45 sK1 sK2 sK0 X1]
  have l47 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l37 sK2 sK1]
    conv => enter [1]; rw [← l36 sK0 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [h54066 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) sK0 sK1 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54066 sK0 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h54066 sK0 sK0 sK1 sK2]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l48 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [← l46 sK2 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l52 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l49 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l53 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l52 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l46 sK2 sK1 sK0 X0]
  have l54 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l53 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l47 sK2 sK1 sK0]
  have l55 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l49 sK0 sK1 sK2]
    conv => enter [1]; rw [← l54 sK0 sK1 sK2 X0]
  have l56 : ∀ X2 sK0 sK1 sK2 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro X2 sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l55 sK0 sK1 sK2 X2]
    conv => enter [1]; rw [h54066 X2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X1]
  have l57 : ∀ X2 sK0 sK1 sK2 X0 X1 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1))) := by
    intro X2 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l56 X2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l40 sK0 sK1 sK2 (X0 ◇ X1)]
  have l58 : ∀ sK2 sK1 X2 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X2 sK0
    conv => enter [1]; rw [l46 sK2 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l57 X2 sK0 sK1 sK2 sK2 sK2]
  have l59 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [l58 sK2 sK1 X2 sK0]
  have l60 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h54066 X0 X1 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l59 sK0 sK1 sK2 X1]
  have l61 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l60 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l59 sK0 sK1 sK2 X1]
  intro x y z
  conv => enter [1]; rw [l61 x y z x y]

theorem Equation4512_54119_implies_Equation54125 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54119 : Equation54119 G) : Equation54125 G := by
  have l0 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l1 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l2 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ X0) ◇ sK0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h54119 sK0 ((sK2 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h54119 sK1 ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54119 (sK2 ◇ sK0) (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [l2 sK2 sK0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54119 X0 X1 X2]
    conv => enter [1]; rw [← h54119 X2 (X0 ◇ X1) X2]
  have l7 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54119 (sK2 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l8 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h54119 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK2]
  have l9 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) X0 sK1]
  have l10 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK2 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54119 sK0 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 X0]
  have l11 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54119 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 sK2]
  have l12 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54119 X0 X1 (sK2 ◇ sK0)]
  have l13 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l11 X0 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))]
  have l14 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 X0]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l16 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) = (sK2 ◇ (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l5 sK2 sK0 sK2]
    conv => enter [1]; rw [← h54119 sK2 ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) sK2]
  have l17 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ sK2) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54119 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 sK2]
  have l18 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h54119 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 sK2]
  have l19 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 X0 sK1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0 sK1]
  have l20 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [← h54119 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) sK1]
  have l21 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ X0) ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← h54119 (sK0 ◇ (sK2 ◇ sK0)) X0 sK0]
  have l22 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l13 X0 sK2 sK0]
    conv => enter [1]; rw [l12 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l23 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l16 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) sK2]
  have l24 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← l19 sK1 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK3)) X0 sK1]
  have l25 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l21 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) X0 sK0]
  have l26 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l22 X0 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l27 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l23 sK2 sK0]
    conv => enter [1]; rw [l12 sK2 sK0 (sK2 ◇ sK0) sK2]
  have l28 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ sK1)]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (X0 ◇ sK0)]
  have l30 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ (((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54119 sK2 ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) sK0]
  have l31 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l27 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 sK2]
  have l32 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK2]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l31 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l34 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l12 sK2 sK0 sK0 sK2]
    conv => enter [1]; rw [← l32 sK0 sK2]
  have l35 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l34 sK0 sK2]
    conv => enter [1]; rw [l29 sK0 sK2 (sK2 ◇ sK0)]
  have l37 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h54119 (sK2 ◇ sK0) sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l36 sK0 sK2]
  have l38 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l37 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 sK0]
  have l39 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l17 sK0 sK2 sK0]
  have l40 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l17 (sK2 ◇ sK0) sK2 sK0]
  have l41 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK0 ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l17 (sK2 ◇ sK0) sK2 sK0]
  have l42 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l17 (sK2 ◇ sK0) sK2 sK0]
  have l43 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK2]
  have l44 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l41 sK2 sK0]
    conv => enter [1]; rw [l0 sK2 sK0 sK2]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2 sK2]
    conv => enter [1]; rw [← l39 sK2 sK0]
  have l46 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 sK2]
  have l47 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l44 sK2 sK0]
    conv => enter [1]; rw [l8 sK2 sK0]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [l7 sK2 sK0 sK0]
  have l49 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l46 sK0 sK2]
    conv => enter [1]; rw [l29 sK0 sK2 sK2]
  have l50 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l47 sK2 sK0]
    conv => enter [1]; rw [← l35 sK0 sK2]
  have l51 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [← l38 sK0 sK2]
  have l52 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l12 sK2 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1]; rw [l50 sK2 sK0]
  have l53 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l52 sK2 sK0]
  have l54 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK2) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l40 sK2 sK0]
    conv => enter [1]; rw [l53 sK2 sK0]
  have l55 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l54 sK2 sK0]
    conv => enter [1]; rw [← l17 sK0 sK2 sK0]
  have l56 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2, 2]; rw [l51 sK0 sK2]
    conv => enter [1]; rw [← h54119 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l51 sK0 sK2]
  have l57 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l51 sK0 sK2]
    conv => enter [1]; rw [← l56 X0 sK0 sK2]
  have l58 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l0 sK2 sK0 sK2]
    conv => enter [1, 2]; rw [← l17 sK0 sK2 sK0]
  have l59 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l8 sK2 sK0]
    conv => enter [1]; rw [l58 sK2 sK0]
  have l60 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l35 sK0 sK2]
    conv => enter [1]; rw [l59 sK0 sK2]
  have l61 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l55 sK0 sK2]
    conv => enter [1]; rw [l60 sK0 sK2]
  have l62 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l49 sK0 sK2]
  have l63 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l62 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) sK2 X0]
  have l64 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l57 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l65 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l57 sK0 sK2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l0 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l66 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l57 sK0 sK2 (sK2 ◇ sK0)]
  have l67 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l63 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l66 sK0 sK2]
  have l68 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l65 sK0 sK2]
    conv => enter [1, 2]; rw [← l51 sK0 sK2]
  have l69 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l64 sK2 sK0]
    conv => enter [1]; rw [← l61 sK0 sK2]
  have l70 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l29 sK0 sK2 sK2]
    conv => enter [1]; rw [l67 sK0 sK2]
  have l71 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l68 sK0 sK2]
    conv => enter [1]; rw [l69 sK2 sK0]
  have l72 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l71 sK0 sK2]
    conv => enter [1]; rw [← l70 sK0 sK2]
  have l73 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l68 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l74 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l71 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l75 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l72 sK0 sK2]
    conv => enter [1]; rw [← l49 sK0 sK2]
  have l76 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l75 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) sK2 X0]
  have l77 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ X0)) = (X0 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [h54119 X0 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [l18 X0 sK2 sK3]
  have l78 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ sK3)) ◇ X1)) = (((sK2 ◇ sK3) ◇ sK2) ◇ X1) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (sK2 ◇ sK3)) X1]
    conv => enter [1, 1]; rw [l18 X0 sK2 sK3]
  have l79 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l18 (sK2 ◇ sK0) sK2 sK3]
    conv => enter [1]; rw [l0 sK2 sK0 (sK2 ◇ sK3)]
  have l80 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3))) = (sK0 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [l18 (sK2 ◇ sK0) sK2 sK3]
  have l81 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ ((sK2 ◇ sK3) ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← l80 sK0 sK2 sK3]
    conv => enter [1]; rw [l63 sK0 sK2 (sK2 ◇ sK3)]
  have l82 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l79 sK2 sK3 sK0]
    conv => enter [1]; rw [← l73 sK0 sK2 (sK2 ◇ sK3)]
  have l83 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ sK3)) ◇ X1)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ X1)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [l78 X0 sK2 sK3 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) sK2 X1]
  have l84 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (sK0 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l76 sK0 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l81 sK0 sK2 sK3]
  have l85 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X1))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ X1)) := by
    intro X0 sK2 sK3 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK2 ◇ sK3) X1]
    conv => enter [1]; rw [l83 X0 sK2 sK3 X1]
  have l86 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (sK0 ◇ ((sK2 ◇ sK3) ◇ sK0)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l84 sK0 sK2 sK3]
    conv => enter [1]; rw [← l77 sK0 sK2 sK3]
  have l87 : ∀ sK2 sK3 X1 : G, ((sK2 ◇ sK3) ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ X1)) := by
    intro sK2 sK3 X1
    conv => enter [1]; rw [h54119 (sK2 ◇ sK3) X1 sK2]
    conv => enter [1]; rw [l85 sK2 sK2 sK3 X1]
  have l88 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK0 ◇ ((sK2 ◇ sK3) ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l82 sK2 sK3 sK0]
    conv => enter [1]; rw [l86 sK0 sK2 sK3]
  have l89 : ∀ sK2 sK3 X1 sK1 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) := by
    intro sK2 sK3 X1 sK1
    conv => enter [1]; rw [← l87 sK2 sK3 X1]
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 X1]
  have l90 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ ((sK2 ◇ sK3) ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [l88 sK2 sK3 sK0]
  have l91 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2, 2]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) sK2 X0]
  have l92 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [l91 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 sK2]
  have l93 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l20 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [l92 sK1 sK1 sK2 sK3]
  have l94 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h54119 (sK2 ◇ sK3) sK0 sK0]
    conv => enter [1, 2]; rw [← l90 sK1 sK2 sK3 sK0]
  have l95 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← l94 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK2 sK3 sK0]
  have l96 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK2 ◇ sK0)) sK2 sK3]
    conv => enter [1, 2]; rw [← l82 sK2 sK3 sK0]
  have l97 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1, 2, 2]; rw [l82 sK2 sK3 sK0]
    conv => enter [1]; rw [← h54119 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK3) X0]
  have l98 : ∀ sK2 sK3 X0 sK0 : G, (((sK2 ◇ sK3) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0 sK0
    conv => enter [1, 1]; rw [l82 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK3) X0]
  have l99 : ∀ sK2 sK3 X0 sK0 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK2 sK3 X0 sK0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) sK2 X0]
    conv => enter [1]; rw [l98 sK2 sK3 X0 sK0]
  have l100 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l97 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [l29 sK0 sK2 (sK2 ◇ sK3)]
  have l101 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK3]
    conv => enter [1]; rw [l96 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l18 sK1 sK2 sK3]
  have l102 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [← l89 sK2 sK3 X0 sK1]
    conv => enter [1]; rw [l99 sK2 sK3 X0 sK0]
  have l103 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK3) ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [h54119 (sK2 ◇ sK3) sK2 sK2]
    conv => enter [1]; rw [l100 sK2 sK2 sK3 sK0]
  have l104 : ∀ sK2 sK3 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [l103 sK2 sK3 sK0]
    conv => enter [1]; rw [← l102 sK1 sK2 sK3 sK0 sK0]
  have l105 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l104 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← l95 sK0 sK1 sK2 sK3]
  have l106 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK2]
    conv => enter [1]; rw [l105 sK2 sK3 sK0 sK1]
  have l107 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ X0)) = (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2 X0]
    conv => enter [1, 1]; rw [← l93 sK1 sK2 sK3]
  have l108 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l107 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 X0]
  have l109 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK0 X0]
    conv => enter [1, 1]; rw [← l95 sK0 sK1 sK2 sK3]
  have l110 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l109 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l111 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l93 sK1 sK2 sK3]
    conv => enter [1]; rw [l106 sK1 sK2 sK3 sK0]
  have l112 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2 X0]
    conv => enter [1, 2, 2]; rw [l106 sK1 sK2 sK3 sK0]
  have l113 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l112 sK1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← h54119 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1]
  have l114 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l113 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← l95 sK0 sK1 sK2 sK3]
  have l115 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l20 sK1 sK1 sK2 sK3]
    conv => enter [1]; rw [← l114 sK1 sK2 sK3 sK1]
  have l116 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l115 sK1 sK2 sK3]
    conv => enter [1]; rw [l28 sK1 sK2 sK3 sK2]
  have l117 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l116 sK1 sK2 sK3]
    conv => enter [1]; rw [l108 sK1 sK2 sK3 sK1]
  have l118 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← l111 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l117 sK1 sK2 sK3]
  have l119 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l20 (sK0 ◇ (sK2 ◇ sK0)) sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l101 sK1 sK2 sK3 sK0]
  have l120 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1)) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1]; rw [h54119 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [l20 X0 sK1 sK2 sK3]
  have l121 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1))) = (X1 ◇ ((X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X1)) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1, 2, 2]; rw [← l20 X1 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54119 X1 (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) X0]
  have l122 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1))) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [l121 X0 sK1 sK2 sK3 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X1]
  have l123 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l120 X0 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [l111 sK1 sK2 sK3 sK0]
  have l124 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l101 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l119 sK1 sK2 sK3 sK1]
  have l125 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [l122 X0 sK1 sK2 sK3 X1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X1 X1]
  have l126 : ∀ sK1 sK2 sK3 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK1 sK1]
    conv => enter [1]; rw [l125 sK1 sK1 sK2 sK3 X1]
  have l127 : ∀ sK1 sK2 sK3 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [← l28 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l126 sK1 sK2 sK3 X1]
  have l128 : ∀ sK0 sK1 sK2 sK3 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [l118 sK0 sK1 sK2 sK3]
    conv => enter [1]; rw [l127 sK1 sK2 sK3 X1]
  have l129 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l124 sK1 sK2 sK3]
    conv => enter [1]; rw [l111 sK1 sK2 sK3 sK0]
  have l130 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l129 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l131 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1, 1]; rw [l129 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l132 : ∀ sK0 sK2 sK1 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l130 sK2 sK1 sK3 sK0]
  have l133 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1, 2, 2]; rw [l130 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l134 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l133 X0 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l135 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l101 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l132 sK0 sK2 sK1 sK3]
  have l136 : ∀ sK0 sK2 sK1 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK0 sK2 sK1 sK3 X0
    conv => enter [1]; rw [l74 sK0 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [← l134 X0 sK2 sK1 sK3 sK0]
  have l137 : ∀ sK0 sK2 sK1 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [l136 sK0 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← h54119 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK0]
  have l138 : ∀ sK0 sK2 sK1 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [l137 sK0 sK2 sK1 sK3]
    conv => enter [1]; rw [l123 sK2 sK1 sK2 sK3 sK0]
  have l139 : ∀ sK0 sK2 sK1 sK3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [l138 sK0 sK2 sK1 sK3]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l140 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l130 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l139 sK0 sK2 sK1 sK3]
  have l141 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l101 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l140 sK2 sK1 sK3 sK1]
  have l142 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l141 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l143 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h54119 (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) sK0 X0]
    conv => enter [1, 2]; rw [← l135 sK1 sK2 sK3 sK0]
  have l144 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ sK0))) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l143 X0 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l145 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ sK0))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l142 sK1 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [← l144 X0 sK2 sK1 sK3 sK0]
  have l146 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ (X0 ◇ (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0)))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l145 sK1 sK2 sK3 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK0]
  have l147 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l146 sK1 sK2 sK3 sK1 sK0]
    conv => enter [1]; rw [← h54119 sK2 ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK0) sK1]
  have l148 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l147 sK1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK0 sK2]
  have l149 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l148 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l142 sK1 sK2 sK3 (sK0 ◇ sK2)]
  have l150 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l149 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l110 sK1 sK2 sK3 sK0 sK2]
  have l151 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK2) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l131 sK1 sK2 sK3 sK2 sK1]
    conv => enter [1]; rw [← l150 sK1 sK2 sK3 sK1]
  have l152 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l93 sK1 sK2 sK3]
    conv => enter [1]; rw [l151 sK1 sK2 sK3]
  have l153 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← l111 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l152 sK1 sK2 sK3]
  have l154 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l129 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [l153 sK1 sK1 sK2 sK3]
  have l155 : ∀ X0 sK1 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3
    conv => enter [1, 2, 2]; rw [l154 sK1 sK2 sK3]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [← l154 sK1 sK2 sK3]
  have l156 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l154 sK1 sK2 sK3]
    conv => enter [1]; rw [← l155 X0 sK1 sK2 sK3]
  have l157 : ∀ sK1 sK2 sK3 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) ◇ X1)) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1, 1]; rw [l156 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) X1]
  have l158 : ∀ sK1 sK2 sK3 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1))) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1]; rw [l157 sK1 sK2 sK3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X1]
  have l159 : ∀ sK1 sK2 sK3 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [l158 sK1 sK2 sK3 X1 sK1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X1 sK1]
  have l160 : ∀ sK1 sK2 sK3 X1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X1 sK0
    conv => enter [1]; rw [l159 sK1 sK2 sK3 X1]
    conv => enter [1]; rw [← l128 sK0 sK1 sK2 sK3 X1]
  have l161 : ∀ sK1 sK2 sK3 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) := by
    intro sK1 sK2 sK3 X1
    conv => enter [1]; rw [l129 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← l160 sK1 sK2 sK3 X1 sK1]
  have l162 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l161 sK1 sK2 sK3 ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l57 sK0 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  intro x y z w
  conv => enter [1]; rw [← l162 z y w x]

theorem Equation4512_54125_implies_Equation54119 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54125 : Equation54125 G) : Equation54119 G := by
  have l0 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h54125 (sK0 ◇ sK0) sK0 X1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h54125 sK0 sK0 X0 (sK1 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [h54125 (sK1 ◇ sK2) sK0 X0 (sK1 ◇ sK2)]
  have l2 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 X1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0 (sK1 ◇ sK2)]
  have l4 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X1 sK0 sK1 sK2 X1]
    conv => enter [1, 2, 2]; rw [← h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 X1 (sK1 ◇ sK2)]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l6 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l4 X1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l6 X1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l8 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l7 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 sK2]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54125 X0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l9 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54125 sK0 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l10 sK0 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
  have l19 : ∀ X1 X0 sK1 sK2 sK0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X0 sK1 sK2 sK0
    conv => enter [1]; rw [h54125 X1 X0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54125 (sK1 ◇ sK2) sK0 X0 (sK1 ◇ sK2)]
  have l20 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [← h54125 (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1 X0 X2]
    conv => enter [1, 2]; rw [← h54125 (sK1 ◇ sK2) sK0 X1 (sK1 ◇ sK2)]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h54125 (sK1 ◇ sK2) sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l20 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ (sK1 ◇ sK2)) ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK1 sK2 sK0]
  have l25 : ∀ X0 X1 X2 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK1 sK2 sK0
    conv => enter [1]; rw [l23 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l19 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) sK1 sK2 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l24 sK0 sK1 sK2]
  have l27 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l25 X0 X1 X2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l29 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l27 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
  have l30 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54125 X0 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54125 sK0 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l30 sK0 sK0 sK1 sK2]
  have l32 : ∀ X2 sK0 X1 X0 sK1 sK2 : G, (X2 ◇ (sK0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X2 sK0 X1 X0 sK1 sK2
    conv => enter [1]; rw [h54125 X2 sK0 X1 X1]
    conv => enter [1, 2]; rw [h54125 X1 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l33 : ∀ X1 X2 X3 sK0 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK0 ◇ X2) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 X2 X3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h54125 (sK0 ◇ X2) X2 X1 X3]
    conv => enter [1, 2]; rw [h54125 X2 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l34 : ∀ X1 X2 X3 sK0 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (sK0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X1 X2 X3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l33 X1 X2 X3 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 X2 (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l35 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← h54125 sK0 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l32 sK0 sK0 X1 X0 sK1 sK2]
  have l36 : ∀ sK0 X2 X0 sK1 sK2 : G, (sK0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X2 X0 sK1 sK2
    conv => enter [1]; rw [← l34 sK0 X2 sK0 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l29 sK0 X2 sK0 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1, 2]; rw [l35 sK0 sK1 sK2 X2 sK0]
    conv => enter [1]; rw [l36 sK0 X2 sK0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 X2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X2]
  have l39 : ∀ sK0 sK1 sK2 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X2]
  have l40 : ∀ X2 X1 X0 sK0 sK1 sK2 : G, (X2 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X2 X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54125 X2 X1 X0 (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h54125 (sK0 ◇ (sK1 ◇ sK2)) sK0 X1 (sK1 ◇ sK2)]
  have l41 : ∀ X2 X1 sK0 sK1 sK2 : G, (X2 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X2 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l40 X2 X1 X2 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 X2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 X2 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 sK1 sK2 X2 X1
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l41 X2 X1 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l44 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 sK1 sK2]
  have l45 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
  have l46 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l45 sK1 sK2 sK1]
    conv => enter [1]; rw [l39 sK1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l45 sK1 sK2 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54125 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 sK0 sK1]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [← l46 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l49 z x y]

theorem Equation4512_54119_implies_Equation54131 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54119 : Equation54119 G) : Equation54131 G := by
  have l0 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ ((sK3 ◇ sK0) ◇ X0)) = (((sK2 ◇ sK3) ◇ sK0) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h4512 sK2 sK3 sK0]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK2 ◇ sK3) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) sK0 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 ((sK3 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) = (sK0 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ sK0) (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK3 sK0 (sK3 ◇ sK0)]
  have l4 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 sK0 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK0 sK3]
  have l5 : ∀ sK0 sK3 X0 X1 : G, (sK0 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ sK0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK3 X0 X1
    conv => enter [1]; rw [h54119 sK0 ((sK3 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK3 ◇ sK0) X0]
  have l6 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h54119 (sK3 ◇ sK0) (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [l4 sK3 sK0]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54119 X0 X1 X2]
    conv => enter [1]; rw [← h54119 X2 (X0 ◇ X1) X2]
  have l8 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ (sK3 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [h54119 (sK3 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK3 ◇ sK0) X0]
  have l9 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h54119 sK3 (sK0 ◇ (sK3 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK3]
  have l10 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← h54119 (sK2 ◇ sK3) X0 sK1]
  have l11 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (X0 ◇ sK3)) = (sK2 ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [h54119 sK3 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK3 X0]
  have l12 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK3 ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [h54119 sK0 X0 sK3]
    conv => enter [1, 2]; rw [h4512 sK3 sK0 X0]
  have l13 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ sK0))) = ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← h54119 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) sK0 X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK3]
  have l14 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [← l2 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54119 X0 X1 (sK3 ◇ sK0)]
  have l15 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ sK0))) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l13 X0 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK3 ◇ sK0)) ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))]
  have l16 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l10 sK1 sK2 sK3 X0]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l18 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0))) = (sK3 ◇ (((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l6 sK3 sK0 sK3]
    conv => enter [1]; rw [← h54119 sK3 ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) sK3]
  have l19 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ sK3) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← h54119 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK3 sK0 sK3]
  have l20 : ∀ X0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [← h54119 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 sK3 sK2]
  have l21 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l5 sK0 sK3 X0 sK0]
    conv => enter [1]; rw [← h54119 (sK0 ◇ (sK3 ◇ sK0)) X0 sK0]
  have l22 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [← h54119 sK0 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK3 ◇ sK0) sK0]
  have l23 : ∀ X0 sK3 sK0 : G, (X0 ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ sK0))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l15 X0 sK3 sK0]
    conv => enter [1]; rw [l14 sK3 sK0 (sK0 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0)]
  have l24 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0))) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l18 sK3 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0) sK3]
  have l25 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK0 ◇ ((sK3 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← l21 sK0 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ sK0) X0 sK0]
  have l26 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [← l23 X0 sK3 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK3 (sK0 ◇ (sK3 ◇ sK0)) sK0]
  have l27 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l24 sK3 sK0]
    conv => enter [1]; rw [l14 sK3 sK0 (sK3 ◇ sK0) sK3]
  have l28 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l25 sK0 sK3 X0]
    conv => enter [1]; rw [h4512 sK0 (sK3 ◇ sK0) (X0 ◇ sK0)]
  have l29 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK3 ◇ (((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0) ◇ sK3)) := by
    intro sK0 sK3
    conv => enter [1]; rw [l26 sK0 sK3 sK0]
    conv => enter [1]; rw [← h54119 sK3 ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0) sK0]
  have l30 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l27 sK3 sK0]
    conv => enter [1]; rw [l8 sK3 sK0 sK3]
  have l31 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l29 sK0 sK3]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK3 ◇ sK0)) sK0 sK3]
  have l32 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l30 sK3 sK0]
    conv => enter [1]; rw [l8 sK3 sK0 (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))]
  have l33 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l14 sK3 sK0 sK0 sK3]
    conv => enter [1]; rw [← l31 sK0 sK3]
  have l34 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l32 sK0 sK3]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK3 ◇ sK0)) sK3]
  have l35 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [l33 sK0 sK3]
    conv => enter [1]; rw [l28 sK0 sK3 (sK3 ◇ sK0)]
  have l36 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h54119 (sK3 ◇ sK0) sK0 (sK0 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l35 sK0 sK3]
  have l37 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l36 sK3 sK0]
    conv => enter [1]; rw [l8 sK3 sK0 sK0]
  have l38 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ ((X0 ◇ (sK3 ◇ sK0)) ◇ X1)) = (((sK3 ◇ sK0) ◇ sK3) ◇ X1) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (sK3 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l19 X0 sK3 sK0]
  have l39 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK3 ◇ ((sK3 ◇ sK0) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 sK0 (sK0 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l19 sK0 sK3 sK0]
  have l40 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ sK3) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l2 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l19 (sK3 ◇ sK0) sK3 sK0]
  have l41 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l2 sK3 sK0 ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l19 (sK3 ◇ sK0) sK3 sK0]
  have l42 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = (sK0 ◇ ((sK3 ◇ sK0) ◇ sK3)) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ sK0) ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l19 (sK3 ◇ sK0) sK3 sK0]
  have l43 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3) := by
    intro sK0 sK3
    conv => enter [1]; rw [l42 sK0 sK3]
    conv => enter [1]; rw [h4512 sK0 (sK3 ◇ sK0) sK3]
  have l44 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)))) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l41 sK3 sK0]
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
  have l45 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l12 sK0 sK3 sK3]
    conv => enter [1]; rw [← l39 sK3 sK0]
  have l46 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ ((X0 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ X1)) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [l38 X0 sK3 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK0) sK3 X1]
  have l47 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3) := by
    intro sK0 sK3
    conv => enter [1, 2]; rw [h4512 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 sK3]
  have l48 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l44 sK3 sK0]
    conv => enter [1]; rw [l9 sK3 sK0]
  have l49 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [l45 sK0 sK3]
    conv => enter [1]; rw [l8 sK3 sK0 sK0]
  have l50 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ (X0 ◇ ((sK3 ◇ sK0) ◇ X1))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ X1)) := by
    intro X0 sK3 sK0 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK3 ◇ sK0) X1]
    conv => enter [1]; rw [l46 X0 sK3 sK0 X1]
  have l51 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l47 sK0 sK3]
    conv => enter [1]; rw [l28 sK0 sK3 sK3]
  have l52 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l48 sK3 sK0]
    conv => enter [1]; rw [← l34 sK0 sK3]
  have l53 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l49 sK0 sK3]
    conv => enter [1]; rw [← l37 sK0 sK3]
  have l54 : ∀ sK3 sK0 X1 : G, ((sK3 ◇ sK0) ◇ (X1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ X1)) := by
    intro sK3 sK0 X1
    conv => enter [1]; rw [h54119 (sK3 ◇ sK0) X1 sK3]
    conv => enter [1]; rw [l50 sK3 sK3 sK0 X1]
  have l55 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l14 sK3 sK0 (sK3 ◇ sK0) (sK3 ◇ sK0)]
    conv => enter [1]; rw [l52 sK3 sK0]
  have l56 : ∀ sK3 sK0 X1 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X1)) := by
    intro sK3 sK0 X1
    conv => enter [1]; rw [← l54 sK3 sK0 X1]
    conv => enter [1]; rw [l8 sK3 sK0 X1]
  have l57 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l2 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l55 sK3 sK0]
  have l58 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l40 sK3 sK0]
    conv => enter [1]; rw [l57 sK3 sK0]
  have l59 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l58 sK3 sK0]
    conv => enter [1]; rw [← l19 sK0 sK3 sK0]
  have l60 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK0 sK3
    conv => enter [1, 2, 2]; rw [l53 sK0 sK3]
    conv => enter [1]; rw [← h54119 (sK0 ◇ (sK3 ◇ sK0)) (sK0 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l53 sK0 sK3]
  have l61 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l53 sK0 sK3]
    conv => enter [1]; rw [← l60 X0 sK0 sK3]
  have l62 : ∀ sK3 sK0 : G, (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l2 sK3 sK0 sK3]
    conv => enter [1, 2]; rw [← l19 sK0 sK3 sK0]
  have l63 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l9 sK3 sK0]
    conv => enter [1]; rw [l62 sK3 sK0]
  have l64 : ∀ sK0 sK3 : G, (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3)) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l34 sK0 sK3]
    conv => enter [1]; rw [l63 sK0 sK3]
  have l65 : ∀ sK0 sK3 : G, (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l59 sK0 sK3]
    conv => enter [1]; rw [l64 sK0 sK3]
  have l66 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK3 ◇ sK0)) ◇ sK3) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK3 ◇ sK0)) (sK3 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l51 sK0 sK3]
  have l67 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l66 sK0 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK3 ◇ sK0)) sK3 X0]
  have l68 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1, 2]; rw [l61 sK0 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 sK0 (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0)))]
  have l69 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = (sK3 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l61 sK0 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l2 sK3 sK0 (sK0 ◇ (sK3 ◇ sK0))]
  have l70 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK3 ◇ sK0) ((sK3 ◇ sK0) ◇ (sK0 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l61 sK0 sK3 (sK3 ◇ sK0)]
  have l71 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l67 sK0 sK3 (sK0 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l70 sK0 sK3]
  have l72 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l69 sK0 sK3]
    conv => enter [1, 2]; rw [← l53 sK0 sK3]
  have l73 : ∀ sK3 sK0 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l68 sK3 sK0]
    conv => enter [1]; rw [← l65 sK0 sK3]
  have l74 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l28 sK0 sK3 sK3]
    conv => enter [1]; rw [l71 sK0 sK3]
  have l75 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l72 sK0 sK3]
    conv => enter [1]; rw [l73 sK3 sK0]
  have l76 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3
    conv => enter [1]; rw [l75 sK0 sK3]
    conv => enter [1]; rw [← l74 sK0 sK3]
  have l77 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1, 1]; rw [l75 sK0 sK3]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK3 ◇ sK0)) X0]
  have l78 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l19 (sK0 ◇ (sK3 ◇ sK0)) sK3 sK0]
    conv => enter [1, 2]; rw [← l76 sK0 sK3]
  have l79 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ sK3) := by
    intro sK0 sK3
    conv => enter [1]; rw [l53 sK0 sK3]
    conv => enter [1]; rw [← l78 sK3 sK0]
  have l80 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK0 sK3
    conv => enter [1, 2, 2]; rw [l79 sK0 sK3]
    conv => enter [1]; rw [← h54119 (sK3 ◇ sK0) sK3 X0]
  have l81 : ∀ X0 sK0 sK3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [l80 X0 sK0 sK3]
    conv => enter [1]; rw [l56 sK3 sK0 (sK3 ◇ sK0)]
  have l82 : ∀ sK0 sK3 X0 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK3 ◇ sK0)))) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l77 sK0 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l81 X0 sK0 sK3]
  have l83 : ∀ sK0 sK3 : G, ((sK0 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK3
    conv => enter [1]; rw [l82 sK0 sK3 sK0]
    conv => enter [1]; rw [l22 sK0 sK0 sK3]
  have l84 : ∀ sK0 sK3 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK3
    conv => enter [1]; rw [l76 sK0 sK3]
    conv => enter [1]; rw [l83 sK0 sK3]
  have l85 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ sK3))) = (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK3 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [l20 sK3 sK2 sK3]
  have l86 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) = ((sK2 ◇ sK3) ◇ (sK0 ◇ ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l20 (sK3 ◇ sK0) sK2 sK3]
    conv => enter [1]; rw [l1 sK2 sK3 sK0 ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3))]
  have l87 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) = ((sK2 ◇ sK3) ◇ (sK0 ◇ ((sK3 ◇ sK0) ◇ sK0))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l86 sK2 sK3 sK0]
    conv => enter [1]; rw [← l17 (sK2 ◇ sK3) sK0 (sK3 ◇ sK0)]
  have l88 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l11 sK3 sK2 sK2]
    conv => enter [1]; rw [← l85 sK2 sK3]
  have l89 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) = ((sK2 ◇ sK3) ◇ ((sK0 ◇ (sK3 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l87 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK3 ◇ sK0) sK0]
  have l90 : ∀ sK3 sK2 sK1 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK3 sK2 sK1
    conv => enter [1]; rw [l88 sK3 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 sK3 sK3]
  have l91 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK3) ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l84 sK0 sK3]
    conv => enter [1]; rw [← l89 sK2 sK3 sK0]
  have l92 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l91 sK2 sK3 sK0]
    conv => enter [1]; rw [← l11 sK3 sK2 sK2]
  have l93 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l61 sK0 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l92 sK2 sK3 sK0]
  have l94 : ∀ sK0 sK3 sK1 sK2 : G, (sK0 ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l93 sK0 sK3 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 sK3 sK3]
  have l95 : ∀ sK0 sK3 sK2 : G, (sK0 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK3 sK2
    conv => enter [1]; rw [l94 sK0 sK3 sK0 sK2]
    conv => enter [1]; rw [← l90 sK3 sK2 sK0]
  have l96 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK3) ◇ sK2) := by
    intro sK3 sK0 sK2
    conv => enter [1, 2]; rw [l95 sK0 sK3 sK2]
    conv => enter [1]; rw [l20 sK3 sK2 sK3]
  have l97 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK3]
    conv => enter [1]; rw [← l96 sK3 sK0 sK2]
  have l98 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l97 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l72 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [← l98 z w y x]

theorem Equation4512_54131_implies_Equation54119 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54131 : Equation54131 G) : Equation54119 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← h54131 X1 X0 sK0 (sK1 ◇ sK2)]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (((sK1 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK0 ((sK1 ◇ sK2) ◇ X0)]
  have l9 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = (((sK2 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l10 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1, 2]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK1 ◇ sK2) (sK1 ◇ X0)]
  have l11 : ∀ sK1 X0 sK0 sK2 : G, ((sK1 ◇ X0) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ X0)]
  have l12 : ∀ sK2 X0 sK1 sK0 : G, ((sK2 ◇ X0) ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1, 2]; rw [← l4 sK2 sK1 X0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK2 ◇ sK1) (sK2 ◇ X0)]
  have l13 : ∀ X1 sK0 sK1 sK2 X0 X2 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X1 sK0 sK1 sK2 X0 X2
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54131 X2 X1 X1 X0]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X2)) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54131 X2 X1 (X0 ◇ X1) X0]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l17 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK2 sK1]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 X1 sK0]
  have l20 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 X1 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 X1 X1]
  have l21 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [h4512 sK2 X0 (sK2 ◇ ((sK1 ◇ sK2) ◇ X0))]
    conv => enter [1]; rw [l12 sK2 X0 sK1 sK0]
  have l22 : ∀ sK1 X0 sK0 sK2 : G, ((sK1 ◇ X0) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l11 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  have l23 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l10 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) X0 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l21 sK2 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2 sK2 (sK1 ◇ sK2) sK0]
  have l27 : ∀ sK1 X0 sK0 sK2 : G, ((sK1 ◇ X0) ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l22 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l23 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l20 sK2 sK0 sK1 sK2 (sK2 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  have l32 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 X0 (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))]
    conv => enter [1]; rw [l27 sK1 X0 sK0 sK2]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [l20 (sK2 ◇ sK1) sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [l20 (sK1 ◇ sK2) sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l18 sK1 sK2 sK0]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l32 sK1 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l20 sK1 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l39 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l35 sK0 sK1 sK2]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l20 sK1 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK0 sK1 sK2]
  have l42 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2 sK1]
    conv => enter [1]; rw [← l39 sK2 sK1 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 (sK1 ◇ sK2)]
  have l45 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
  have l46 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l42 sK2 sK1 sK0]
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
  have l47 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l45 sK2 sK1 sK0]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l46 sK2 sK1 sK0]
  have l49 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l18 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2 X0]
  have l50 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← l49 sK1 sK2 X0 sK0]
  have l51 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 sK2 (sK1 ◇ sK2)]
  have l52 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1 sK2 sK1]
    conv => enter [1]; rw [← l51 sK1 sK2 sK1]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l55 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l42 sK2 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 sK2]
  have l56 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l55 sK2 sK1 sK0]
  have l57 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l52 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l58 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l50 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l57 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l50 sK0 sK1 sK2 X0]
  have l59 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l58 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l20 (sK1 ◇ sK2) sK0 sK1 sK2 X0]
  have l60 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l59 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l60 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l42 sK2 sK1 sK0]
  have l62 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [← l61 sK0 sK1 sK2 X0]
  have l63 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h54131 sK1 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l64 : ∀ X2 X1 X0 sK0 sK1 sK2 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X2 X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54131 X2 X1 X1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h54131 X1 (sK1 ◇ sK2) X0 sK0]
  have l65 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h54131 sK0 (sK1 ◇ sK2) X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l66 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l42 sK2 sK1 sK0]
    conv => enter [1]; rw [← l65 X0 sK0 sK1 sK2]
  have l67 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [l64 sK0 X1 X0 sK0 sK1 sK2]
  have l68 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l66 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [l63 sK2 sK2 sK1 sK2]
  have l69 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l67 sK0 sK1 sK2 X1 sK0]
    conv => enter [1, 2]; rw [l63 sK0 sK0 sK1 sK2]
  have l70 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1]; rw [l68 sK2 sK1]
  have l71 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l62 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [l69 sK1 sK1 sK2 X1]
  have l72 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l71 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← l70 sK1 sK2]
  have l73 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l47 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l74 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l73 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l20 (sK0 ◇ (sK1 ◇ sK2)) sK0 sK1 sK2 X0]
  have l75 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l74 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  have l76 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l75 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
  have l77 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK2 sK1]
    conv => enter [1]; rw [← l76 sK1 sK2 X0 sK1]
  have l78 : ∀ X1 X2 X3 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (((sK0 ◇ (sK1 ◇ sK2)) ◇ X3) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro X1 X2 X3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h54131 ((sK0 ◇ (sK1 ◇ sK2)) ◇ X3) X3 X1 X2]
    conv => enter [1, 2]; rw [h54131 X3 (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
  have l79 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l77 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [h54131 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2)) X0 sK0]
  have l80 : ∀ X1 X2 X3 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))))) := by
    intro X1 X2 X3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l78 X1 X2 X3 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X3 (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l81 : ∀ X1 X2 X3 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X3 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 X2 X3 sK0 sK1 sK2
    conv => enter [1]; rw [l80 X1 X2 X3 sK0 sK1 sK2 X1]
    conv => enter [1, 2, 2]; rw [← l79 sK1 sK2 X1 sK0]
  have l82 : ∀ X1 X2 X3 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X2 X3 sK0 sK1 sK2
    conv => enter [1]; rw [l81 X1 X2 X3 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l72 sK1 sK2 X3]
  have l83 : ∀ X1 X2 X3 sK1 sK2 : G, (X1 ◇ (X1 ◇ (X2 ◇ X3))) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 X3 sK1 sK2
    conv => enter [1]; rw [l82 X1 X2 X3 X1 sK1 sK2]
    conv => enter [1]; rw [← l56 sK1 sK2 X1]
  intro x y z
  conv => enter [1]; rw [← l83 z x y x y]

theorem Equation4512_54119_implies_Equation54134 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54119 : Equation54119 G) : Equation54134 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ sK1)) = (X1 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54119 sK1 ((sK0 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54119 X2 X1 X1]
    conv => enter [1, 2]; rw [h54119 X1 X2 X0]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54119 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54119 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l6 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ sK1))) = (((sK0 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← h54119 ((sK0 ◇ sK1) ◇ X0) sK1 X1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l7 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l6 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l8 : ∀ X0 sK3 sK4 : G, (X0 ◇ (X0 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ sK3) := by
    intro X0 sK3 sK4
    conv => enter [1]; rw [← h54119 sK3 sK4 X0]
    conv => enter [1]; rw [h4512 sK3 sK4 sK3]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK0 ◇ sK1)) X0 sK1]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54119 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54119 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l12 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l7 X1 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) X0 sK1]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l9 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ sK1) ◇ ((X0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← h54119 (sK0 ◇ sK1) (X0 ◇ sK1) sK0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (X0 ◇ sK1)]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 sK1 (X0 ◇ sK1)]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK1) sK1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l17 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l11 sK1 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l11 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK0 ◇ sK1)]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [← l18 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54119 (sK1 ◇ (sK0 ◇ sK1)) sK1 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 sK1]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK0 ◇ sK1)) sK1 sK1]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l31 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← h54119 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l32 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← l31 X0 sK1 sK0]
  have l33 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l32 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X1]
  have l34 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l33 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
  have l35 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l34 sK1 sK0 X1 sK1]
    conv => enter [1]; rw [← h54119 (sK1 ◇ (sK0 ◇ sK1)) X1 sK1]
  have l36 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [l32 sK1 sK0 X0]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK0 ◇ sK1)) X0 X0]
  have l37 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l35 sK1 sK0 X0]
    conv => enter [1]; rw [← l36 X0 sK1 sK0]
  have l38 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l32 sK1 sK0 X0]
    conv => enter [1]; rw [← l37 sK1 sK0 X0]
  have l39 : ∀ sK1 sK0 sK3 sK4 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK3 ◇ sK4) ◇ sK3) := by
    intro sK1 sK0 sK3 sK4
    conv => enter [1]; rw [l38 sK1 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ sK4))]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK0 ◇ sK1)) sK3 sK4]
  have l40 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3 sK4]
    conv => enter [1]; rw [← l39 sK1 sK0 sK3 sK4]
  intro x y z w u
  conv => enter [1]; rw [← l40 z w u x y]

theorem Equation4512_54134_implies_Equation54119 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54134 : Equation54134 G) : Equation54119 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [h54134 sK1 sK2 X0 sK0 (sK1 ◇ sK2)]
  have l1 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l0 sK1 sK2 X0 sK0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← h54134 X0 X1 sK1 sK1 (sK1 ◇ sK2)]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54134 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l3 z x y]

@[equational_result]
theorem Equation54408_implies_Equation54391 (G : Type*) [Magma G] (h54408 : Equation54408 G) : Equation54391 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54408 X0 X1 X2]
    conv => enter [1]; rw [h54408 X1 X1 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [← h54408 X0 X1 X2]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h54408 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [h54408 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h54408 sK1 sK1 sK2]
    conv => enter [1]; rw [h54408 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54408 sK1 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [h54408 sK1 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2]
  have l5 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54408 sK1 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l6 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 X0 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54408 sK0 sK1 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
  have l10 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK2]
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l10 sK1 sK0 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54408 sK1 sK0 (sK0 ◇ sK2)]
  have l13 : ∀ X1 sK1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))))) = (X0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X1 sK1 X0 sK0 sK2
    conv => enter [1, 2, 2]; rw [h54408 sK1 X0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h54408 X0 X1 (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l14 : ∀ X1 sK1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X1 sK1 X0 sK0 sK2
    conv => enter [1]; rw [l13 X1 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [← l0 X1 X0 (sK1 ◇ (sK0 ◇ sK2))]
  have l15 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 sK1 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
  have l16 : ∀ sK1 X1 X0 sK0 sK2 : G, (sK1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK2)))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 X1 X0 sK0 sK2
    conv => enter [1]; rw [h54408 sK1 X1 (X0 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l14 X1 sK1 X0 sK0 sK2]
  have l17 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2, 2]; rw [l15 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54408 sK1 X0 (sK0 ◇ (sK0 ◇ sK2))]
  have l18 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l17 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l16 sK1 X0 sK0 sK0 sK2]
  have l19 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l10 sK1 sK0 sK2]
    conv => enter [1]; rw [← l18 X0 sK1 sK0 sK2]
  have l20 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54408 sK0 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l7 X0 sK0 sK1 sK2]
  have l21 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54408 X0 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l20 sK0 X0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK2]
  have l23 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [h54408 sK1 X0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l19 X0 sK1 sK0 sK2]
  have l24 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54408 X0 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l23 sK1 X0 sK0 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54408 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h54408 sK0 sK1 sK2]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK1 sK0 sK2]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l11 sK1 sK0 sK2]
    conv => enter [1]; rw [← l27 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

@[equational_result]
theorem Equation54391_implies_Equation54408 (G : Type*) [Magma G] (h54391 : Equation54391 G) : Equation54408 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54391 X0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h54391 X0 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1]; rw [← h54391 X0 X2 X1]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54391 sK0 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [h54391 sK0 sK0 (sK1 ◇ sK2)]
  have l3 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [h54391 sK0 X0 (sK1 ◇ sK2)]
  have l4 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [h54391 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h54391 sK0 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l5 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l3 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 X0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54391 sK0 sK1 sK2]
    conv => enter [1]; rw [h54391 sK1 sK0 (sK0 ◇ sK2)]
  have l7 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (X1 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h54391 X0 X1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2, 2]; rw [← h54391 sK1 X0 (sK0 ◇ sK2)]
  have l8 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l7 X0 X1 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l1 X0 sK1 (sK0 ◇ sK2)]
  have l9 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54391 sK0 X0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l9 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 X0 sK1 sK0 sK2]
  have l11 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l10 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54391 sK0 X0 (sK1 ◇ (sK0 ◇ sK2))]
  have l12 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l3 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 X0 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK0 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK2]
  have l15 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h54391 sK1 sK0 sK2]
    conv => enter [1]; rw [h54391 sK0 sK1 (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l15 sK1 sK0 sK2]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]
  conv => enter [1]; rw [l14 y x z]

theorem Equation4512_54270_implies_Equation54282 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54270 : Equation54270 G) : Equation54282 G := by
  have l0 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ sK3) ◇ X0)) = (((sK2 ◇ sK3) ◇ sK3) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK3) X0]
    conv => enter [1, 1]; rw [h4512 sK2 sK3 sK3]
  have l1 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ sK3) ◇ X0)) = ((sK2 ◇ sK3) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l0 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) sK3 X0]
  have l2 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ X0)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK3 X0]
  have l3 : ∀ sK2 sK3 X0 : G, (sK2 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h54270 sK2 (sK3 ◇ sK3) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK3 sK3]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54270 X2 X2 X1]
    conv => enter [1, 2]; rw [h54270 X1 X2 X0]
  have l5 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK2 ◇ sK3) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← h54270 (sK2 ◇ sK3) X0 sK1]
  have l6 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK3 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54270 X0 X1 sK3]
  have l7 : ∀ sK3 X0 X1 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ (X0 ◇ X1))) = (sK3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h54270 X0 X1 sK3]
  have l8 : ∀ sK3 X0 X1 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (X0 ◇ X1))) = (sK3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK3 X0 X1
    conv => enter [1]; rw [← l2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [l7 sK3 X0 X1]
  have l9 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l5 sK1 sK2 sK3 X0]
  have l10 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK2 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [h54270 (sK2 ◇ sK3) sK3 sK2]
    conv => enter [1]; rw [← l3 sK2 sK3 sK2]
  have l11 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ sK3) = (X0 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 sK3]
    conv => enter [1]; rw [h54270 sK2 sK3 X0]
  have l12 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l10 sK2 sK3]
    conv => enter [1]; rw [l1 sK2 sK3 (sK3 ◇ sK3)]
  have l13 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← l12 sK2 sK3]
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 sK3]
  have l14 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1, 2]; rw [h54270 sK3 sK3 sK3]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK3 ◇ (sK3 ◇ sK3))]
  have l15 : ∀ sK2 sK3 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l14 sK2 sK3]
    conv => enter [1]; rw [l13 sK2 sK3 sK1]
  have l16 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l15 sK2 sK3 sK1]
  have l17 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ X0)) = (((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK3 X0]
    conv => enter [1, 1]; rw [← l16 sK2 sK3 sK1]
  have l18 : ∀ sK2 sK3 X0 sK1 : G, ((sK2 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 X0 sK1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) (sK3 ◇ sK3) X0]
    conv => enter [1]; rw [← l17 sK1 sK2 sK3 X0]
  have l19 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK3 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1, 2]; rw [h4512 sK3 sK3 sK3]
    conv => enter [1]; rw [l18 sK2 sK3 sK3 sK1]
  have l20 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l13 sK2 sK3 sK1]
    conv => enter [1]; rw [l19 sK2 sK3 sK1]
  have l21 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l16 sK2 sK3 sK1]
    conv => enter [1]; rw [l20 sK1 sK2 sK3]
  have l22 : ∀ sK3 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [h54270 sK3 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l21 sK2 sK3 sK1]
  have l23 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ sK3)) = (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1, 2]; rw [l11 sK2 sK3 X0]
    conv => enter [1]; rw [← h54270 X0 (sK2 ◇ sK3) X0]
  have l24 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK3 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l11 sK2 sK3 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 (sK2 ◇ sK3)]
  have l25 : ∀ sK3 sK2 : G, (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ sK3)))) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l2 sK3 (sK3 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l11 sK2 sK3 sK3]
  have l26 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l6 sK3 (sK2 ◇ sK3) sK3]
    conv => enter [1]; rw [← l25 sK3 sK2]
  have l27 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK3 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l26 sK2 sK3]
    conv => enter [1]; rw [l8 sK3 sK3 (sK2 ◇ sK3)]
  have l28 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l27 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK3 ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))]
  have l29 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l28 sK2 sK3]
    conv => enter [1]; rw [l6 sK3 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l30 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l29 sK2 sK3]
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 (sK2 ◇ sK3)]
  have l31 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK3]
    conv => enter [1]; rw [l30 sK2 sK3 sK1]
  have l32 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l16 sK2 sK3 sK1]
    conv => enter [1]; rw [l31 sK1 sK2 sK3]
  have l33 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK2 ◇ sK3) ◇ (sK3 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [← l11 sK2 sK3 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) sK3 X0]
  have l34 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK3 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l11 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [← l24 sK2 sK3]
  have l35 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l34 sK2 sK3]
    conv => enter [1]; rw [l6 sK3 (sK2 ◇ sK3) sK3]
  have l36 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l35 sK2 sK3]
    conv => enter [1]; rw [← l33 sK1 sK2 sK3 sK3]
  have l37 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ sK3) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l11 sK2 sK3 sK1]
    conv => enter [1]; rw [l36 sK2 sK3 sK1]
  have l38 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l37 sK1 sK2 sK3]
    conv => enter [1]; rw [← l16 sK2 sK3 sK1]
  have l39 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ sK3) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l11 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l32 sK2 sK3 sK1]
  have l40 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1, 2, 2]; rw [l32 sK2 sK3 sK1]
    conv => enter [1]; rw [← h54270 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK2 ◇ sK3) X0]
  have l41 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ sK3)) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l40 X0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l23 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) sK2 sK3]
  have l42 : ∀ sK2 sK3 : G, ((sK2 ◇ sK3) ◇ sK3) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l39 sK2 sK3 sK2]
    conv => enter [1]; rw [← l22 sK3 sK2 sK2]
  have l43 : ∀ X0 sK2 sK3 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X0 sK2 sK3 sK1
    conv => enter [1]; rw [l41 X0 sK2 sK3 sK1]
    conv => enter [1, 2]; rw [l11 sK2 sK3 sK1]
  have l44 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l11 sK2 sK3 sK1]
    conv => enter [1]; rw [l42 sK2 sK3]
  have l45 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [h54270 (sK2 ◇ sK3) (sK3 ◇ sK3) sK2]
    conv => enter [1]; rw [l43 sK2 sK2 sK3 sK1]
  have l46 : ∀ sK1 sK2 sK3 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l9 sK1 sK2 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l45 sK2 sK3 sK1]
  have l47 : ∀ sK2 sK3 sK1 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ sK3)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK2 sK3 sK1
    conv => enter [1]; rw [l21 sK2 sK3 sK1]
    conv => enter [1]; rw [l46 sK1 sK2 sK3]
  have l48 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l38 sK1 sK2 sK3]
    conv => enter [1]; rw [l47 sK2 sK3 sK1]
  have l49 : ∀ sK3 sK1 sK2 : G, ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK3 sK1 sK2
    conv => enter [1]; rw [← h4512 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1, 2]; rw [← l44 sK1 sK2 sK3]
  have l50 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l44 sK1 sK2 sK3]
    conv => enter [1]; rw [h54270 sK3 sK3 sK3]
    conv => enter [1, 2]; rw [← l44 sK1 sK2 sK3]
  have l51 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK3 ◇ sK3) ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l50 sK1 sK2 sK3]
    conv => enter [1]; rw [← l49 sK3 sK1 sK2]
  have l52 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l48 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0]
  have l53 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 1]; rw [l51 sK1 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK3) (sK3 ◇ sK3) X0]
  have l54 : ∀ sK3 X0 : G, (sK3 ◇ (sK3 ◇ ((sK3 ◇ sK3) ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK3 X0
    conv => enter [1, 2, 2]; rw [← h4512 sK3 sK3 X0]
    conv => enter [1]; rw [← l4 X0 sK3 sK3]
  have l55 : ∀ sK3 X0 : G, ((sK3 ◇ sK3) ◇ ((sK3 ◇ sK3) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK3 X0
    conv => enter [1]; rw [← h4512 sK3 sK3 ((sK3 ◇ sK3) ◇ X0)]
    conv => enter [1]; rw [l54 sK3 X0]
  have l56 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l53 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l55 sK3 X0]
  have l57 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l48 sK1 sK2 sK3]
  have l58 : ∀ sK1 sK2 sK3 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) ◇ X1) = ((sK2 ◇ sK3) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1, 1]; rw [l9 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK3) (X0 ◇ X0) X1]
  have l59 : ∀ sK1 sK2 sK3 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) ◇ X1) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l58 sK1 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l60 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X0 X1]
    conv => enter [1]; rw [l59 sK1 sK2 sK3 X0 X1]
  have l61 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK2 ◇ sK3) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l4 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK2 ◇ sK3) X0]
    conv => enter [1, 2, 2, 2]; rw [← l57 sK1 sK2 sK3]
  have l62 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l61 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← l60 sK1 sK2 sK3 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l63 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l52 sK1 sK2 sK3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
    conv => enter [1]; rw [l62 sK1 sK2 sK3 X0]
  have l64 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
    conv => enter [1]; rw [l63 sK1 sK2 sK3 X0]
  have l65 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1, 2]; rw [l64 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h54270 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l66 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK3]
    conv => enter [1]; rw [l65 sK1 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← l48 sK1 sK2 sK3]
  have l67 : ∀ sK1 sK2 sK3 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1)) := by
    intro sK1 sK2 sK3 X1 X0
    conv => enter [1, 1]; rw [l66 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) X1]
  have l68 : ∀ X1 X0 sK1 sK2 sK3 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK1 sK2 sK3
    conv => enter [1]; rw [l4 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l56 sK1 sK2 sK3 (X0 ◇ X1)]
  have l69 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l67 sK1 sK2 sK3 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l68 X1 X0 sK1 sK2 sK3]
  have l70 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X1) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l69 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l56 sK1 sK2 sK3 X1]
  have l71 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1, 2]; rw [← l70 sK1 sK2 sK3 X1 X0]
    conv => enter [1]; rw [← h54270 X1 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))]
  have l72 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l52 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l71 sK1 sK2 sK3 X0 X1]
  have l73 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l37 sK1 sK2 sK3]
    conv => enter [1]; rw [l72 sK1 sK2 sK3 sK3 X0]
  intro x y z w
  conv => enter [1]; rw [← l73 z w y x]

@[equational_result]
theorem Equation54282_implies_Equation54270 (G : Type*) [Magma G] (h54282 : Equation54282 G) : Equation54270 G := by
  have l0 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54282 X1 sK2 X1 sK2]
    conv => enter [1]; rw [← h54282 X0 sK2 X1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54282 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 z x y]

end Semigroup5
