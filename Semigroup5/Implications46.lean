import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54067_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54034 G := by
  have l0 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54067 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54067 (sK2 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h54067 (sK1 ◇ sK0) X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54067 X0 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54067 X0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 (X0 ◇ X0)]
  have l9 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54067 X0 sK2 (sK1 ◇ sK0)]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l8 X0 sK1 sK0 X0]
    conv => enter [1]; rw [← h54067 X0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l12 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l1 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [l13 X1 X0 X2]
  have l15 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 (sK1 ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l18 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l15 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l20 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l9 sK2 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK2 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l22 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK1 ◇ sK0)]
  have l24 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK0 sK2]
    conv => enter [1]; rw [← l5 sK1 sK0 (sK1 ◇ sK0) sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l23 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 sK0 sK0 sK2]
  have l26 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l27 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
  have l28 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l24 sK1 sK0 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l24 sK1 sK0 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l28 sK2 sK1 sK0]
  have l32 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l33 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l31 sK2 sK1 sK0]
    conv => enter [1]; rw [l9 sK2 sK1 sK0 (sK1 ◇ sK0)]
  have l34 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l5 sK1 sK0 sK0 sK2]
    conv => enter [1]; rw [l32 sK1 sK0 sK2]
  have l35 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l34 sK0 sK2 sK1]
  have l36 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [l35 sK0 sK2 sK1]
  have l37 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l33 sK2 sK1 sK0]
  have l38 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l37 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
  have l39 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [← l38 sK0 sK2 sK1]
  have l40 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l41 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l40 sK1 sK0 sK2 X0]
  have l42 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l39 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l43 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l42 sK1 sK0 sK2 X0]
  have l44 : ∀ sK2 sK1 sK0 X0 X1 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X1) = (X0 ◇ (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro sK2 sK1 sK0 X0 X1
    conv => enter [1, 1]; rw [l3 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ sK0))) X1]
  have l45 : ∀ sK2 sK1 sK0 X0 X1 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK2 sK1 sK0 X0 X1
    conv => enter [1]; rw [l44 sK2 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ sK0)) X1]
  have l46 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l39 sK1 sK0 sK2]
  have l47 : ∀ sK2 sK1 sK0 X0 X1 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK2 sK1 sK0 X0 X1
    conv => enter [1]; rw [l45 sK2 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l43 sK1 sK0 sK2 X1]
  have l48 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l46 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
  have l49 : ∀ sK2 sK1 sK0 X0 X1 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK2 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X1]
    conv => enter [1]; rw [l47 sK2 sK1 sK0 X0 X1]
  have l50 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [← l48 sK2 sK1 sK0]
  have l51 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [← l49 sK2 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ (sK1 ◇ sK0)) X1]
  have l52 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l50 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X0]
  have l53 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l52 sK1 sK0 sK2 X0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK1]
  have l55 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l4 sK0 sK2 sK1]
  have l56 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
  have l57 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l56 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l58 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l57 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l4 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK1]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l58 sK1 sK0 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
  have l61 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l54 sK0 sK1]
  have l62 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)]
    conv => enter [1, 2]; rw [← l60 sK0 sK1 sK2]
  have l63 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l61 sK0 sK2 sK1]
    conv => enter [1]; rw [← l62 sK2 sK1 sK0]
  have l64 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l63 sK0 sK2 sK1]
    conv => enter [1]; rw [← l53 sK1 sK0 sK2 sK0]
  have l65 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l55 sK2 sK1 sK0]
    conv => enter [1]; rw [l64 sK0 sK2 sK1]
  have l66 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l65 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l67 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l66 sK0 sK2 sK1]
    conv => enter [1]; rw [← l41 sK1 sK0 sK2 sK0]
  have l68 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l65 sK2 sK1 sK0]
    conv => enter [1]; rw [← l67 sK0 sK2 sK1]
  have l69 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l68 sK2 sK1 sK0]
  have l70 : ∀ sK2 sK1 sK0 X0 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (X0 ◇ (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l12 ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l65 sK2 sK1 sK0]
  have l71 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l55 sK2 sK1 sK0]
  have l72 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l73 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 (sK1 ◇ sK0) sK2 X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l74 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l10 sK0 sK1 sK0]
    conv => enter [1]; rw [l72 sK0 sK1 X0]
  have l75 : ∀ sK2 sK1 sK0 X0 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l70 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) sK0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l76 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l74 sK0 sK1 X0]
  have l77 : ∀ sK2 sK1 sK0 X0 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l75 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l51 sK0 sK1 sK0 sK2 sK0]
  have l78 : ∀ sK2 sK1 sK0 X0 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l77 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l79 : ∀ sK2 sK1 sK0 X0 : G, (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l78 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l41 sK1 sK0 sK2 sK0]
  have l80 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l76 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l79 sK2 sK1 sK0 X0]
  have l81 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l80 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) sK0 (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))]
  have l82 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l81 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l14 sK0 X0 (sK2 ◇ (sK1 ◇ sK0))]
  have l83 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l12 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l82 X0 sK0 sK1 sK2]
  have l84 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [l83 sK0 sK2 sK1 X0]
  have l85 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l69 sK0 sK2 sK1]
    conv => enter [1]; rw [l84 sK0 sK2 sK1 X0]
  have l86 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [l69 sK0 sK2 sK1]
  have l87 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l71 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l86 sK1 sK0 sK2]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1 sK0]
    conv => enter [1]; rw [← l76 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l89 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK0 sK1 sK1]
    conv => enter [1]; rw [l88 sK0 sK1]
  have l90 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l89 sK1 sK0]
  have l91 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l55 sK2 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
  have l92 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l93 : ∀ sK0 X1 X0 sK1 : G, (sK0 ◇ (X1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [l12 sK0 X1 X0]
    conv => enter [1, 2]; rw [l12 sK0 X0 sK1]
  have l94 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l4 sK0 sK0 sK1]
  have l95 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l94 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 sK1]
  have l96 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l93 sK0 X1 X0 sK1]
    conv => enter [1]; rw [l12 sK0 X1 sK1]
  have l97 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0]
    conv => enter [1]; rw [← l92 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [l95 sK1 sK0]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l100 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK1 sK1]
  have l101 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l96 X0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l100 sK0 sK1 X0]
  have l102 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l101 X0 sK0 sK1]
    conv => enter [1]; rw [l96 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK1]
  have l103 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l99 sK0 sK1]
  have l104 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l103 sK1 sK0 sK2]
    conv => enter [1]; rw [l95 sK1 sK0]
  have l105 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l95 sK1 sK0]
  have l106 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l105 sK2 sK1 sK0]
    conv => enter [1]; rw [l96 sK2 sK0 sK0 sK1]
  have l107 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l91 sK2 sK1 sK0]
    conv => enter [1]; rw [← l106 sK2 sK1 sK0]
  have l108 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l73 sK1 sK0 sK2 sK0]
    conv => enter [1]; rw [← l107 sK2 sK1 sK0]
  have l109 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l108 sK1 sK0 sK2]
    conv => enter [1]; rw [l104 sK1 sK0 sK2]
  have l110 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l99 sK0 sK1]
    conv => enter [1]; rw [l98 sK1 sK0]
  have l111 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ sK0)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l91 sK2 sK1 sK0]
  have l112 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l111 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l41 sK1 sK0 sK2 sK0]
  have l113 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l112 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l76 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l114 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l113 sK0 sK1 X0]
    conv => enter [1]; rw [← l85 sK2 sK1 sK0 X0]
  have l115 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l114 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l109 sK0 sK1 sK0]
  have l116 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l110 sK0 sK1]
    conv => enter [1]; rw [← l115 sK0 sK1 X0]
  have l117 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l116 sK0 sK1 sK0]
    conv => enter [1]; rw [l96 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0 sK1]
  have l118 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l117 sK0 sK1]
    conv => enter [1]; rw [← l102 X0 sK0 sK1]
  have l119 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l12 sK0 X0 sK1]
    conv => enter [1]; rw [l14 sK0 X0 sK1]
  have l120 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l118 sK0 sK1 X0]
    conv => enter [1]; rw [l119 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l120 x y z]

theorem Equation4512_54067_implies_Equation54088 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54088 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54067 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l4 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK1 ◇ sK0)) X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54067 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54067 X0 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54067 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ X0)]
  have l9 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X0)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54067 X0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l8 X0 sK1 sK0]
    conv => enter [1]; rw [← h54067 X0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l12 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l13 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l1 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l14 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l15 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l12 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1]; rw [l14 X1 X0 X2]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l15 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l18 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l17 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X3]
  have l19 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l20 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l19 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l21 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l16 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l20 X0 X1 sK0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l2 sK1 sK0 sK0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l23 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l25 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ (X0 ◇ sK0)) ◇ X1) = (X0 ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1 sK1
    conv => enter [1, 1]; rw [l3 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ sK0) ◇ sK0) X1]
  have l26 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((X0 ◇ X1) ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK0) ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK0]
  have l29 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← l26 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l30 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ (X0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l25 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) sK0 X1]
  have l31 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [← l29 X0 X1 sK1 sK0]
  have l32 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1]; rw [l30 sK0 X0 X1 sK1]
  have l33 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l32 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l34 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK0 sK2]
  have l35 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l36 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l35 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l37 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l36 sK2 sK0 sK1]
  have l39 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l37 sK1 sK0 sK2]
    conv => enter [1]; rw [l33 (sK1 ◇ sK0) sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK2]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l39 sK1 sK0 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK1 ◇ sK0) sK0]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l44 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2]
  have l46 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l42 sK0 sK1 sK2]
  have l47 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l46 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l48 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l47 sK2 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) = (((sK1 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 (sK1 ◇ sK0)]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 (sK1 ◇ sK0) sK0 sK0]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l52 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK1 ◇ sK0) ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l56 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ sK0) sK1]
    conv => enter [1]; rw [← l58 sK0 sK1]
  have l61 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l60 sK0 sK1]
  have l63 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l61 sK1 sK0 sK2]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
  have l66 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l67 : ∀ sK0 sK1 X0 sK2 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l68 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l67 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l69 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l66 sK2 sK0 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1 sK2]
  have l70 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [← l69 sK2 sK0 sK1]
  have l71 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l72 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l64 sK0 sK1]
  have l73 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l72 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l74 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l73 sK2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l75 : ∀ sK2 sK0 sK1 : G, (((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l74 sK2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l76 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
    conv => enter [1]; rw [l75 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
  have l77 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l76 sK2 sK0 sK1]
    conv => enter [1]; rw [l68 sK0 sK1 sK2 (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))]
  have l78 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l77 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l79 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l78 sK2 sK0 sK1]
  have l80 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l81 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l80 sK0 sK1 sK2]
    conv => enter [1]; rw [← l74 sK2 sK0 sK1]
  have l82 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l81 sK0 sK1 sK2]
  have l83 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l82 sK0 sK1 sK2]
  have l84 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l85 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l10 sK0 sK1 sK0]
    conv => enter [1]; rw [l84 sK0 sK1 X0]
  have l86 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l85 sK0 sK1 X0]
  have l87 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l13 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [← l74 sK2 sK0 sK1]
  have l88 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l13 sK0 X0 sK1]
  have l89 : ∀ sK0 X1 X0 sK1 : G, (sK0 ◇ (X1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2]; rw [l13 sK0 X0 sK1]
  have l90 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l13 sK0 X1 sK1]
    conv => enter [1]; rw [l89 sK0 X1 X0 sK1]
  have l91 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l86 sK0 sK1 X0]
    conv => enter [1]; rw [l88 sK1 sK0 X0]
  have l92 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l87 sK2 sK0 sK1]
    conv => enter [1]; rw [← l83 sK0 sK1 sK2]
  have l93 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l90 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l91 sK0 sK1 sK1]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1 sK0]
    conv => enter [1]; rw [l92 sK0 sK0 sK1]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK1]
    conv => enter [1]; rw [l93 sK1 sK0]
  have l96 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l95 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l97 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l96 sK2 sK0 sK1]
    conv => enter [1]; rw [← l83 sK0 sK1 sK2]
  have l98 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l97 sK2 sK0 sK1]
    conv => enter [1]; rw [← l94 sK0 sK1]
  have l99 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l93 sK1 sK0]
    conv => enter [1]; rw [← l94 sK0 sK1]
  have l100 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK1]
    conv => enter [1]; rw [l99 sK1 sK0]
  have l101 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l100 sK0 sK1]
    conv => enter [1]; rw [← l98 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l101 x y z]

theorem Equation4512_54067_implies_Equation54047 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54047 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_54067_implies_Equation54060 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54060 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h54067 (sK0 ◇ sK1) sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l12 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l13 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54067 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54067 X0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X0)]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l19 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l12 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l20 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l18 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1]; rw [l20 X1 X0 X2]
  have l22 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ ((X0 ◇ X1) ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l13 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK1) ◇ sK1)]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l22 sK1 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l25 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l21 sK1 X0 X1]
    conv => enter [1]; rw [← l23 X0 X1 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 X0]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l28 sK0 sK1 X0]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [l13 sK1 X0 sK0]
  have l32 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0 X0]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l32 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l33 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l17 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l37 sK0 sK1]
    conv => enter [1, 2]; rw [l27 sK1 sK0 (sK0 ◇ sK1)]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l40 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l34 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l34 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l34 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l42 sK1 sK0]
    conv => enter [1]; rw [l17 (sK1 ◇ (sK0 ◇ sK1)) sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1, 2]; rw [← l41 sK1 sK0]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1, 2]; rw [← l41 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l27 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l34 sK1 sK0 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l47 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l47 sK1 sK0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [l50 sK1 sK0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l47 sK1 sK0]
    conv => enter [1]; rw [l51 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l49 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l54 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l56 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54067 (sK1 ◇ (sK0 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l39 sK0 sK1]
  have l57 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l56 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l55 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l49 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK1]
  have l62 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l63 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l13 sK1 sK0 sK0]
    conv => enter [1]; rw [l62 sK1 sK0 X0]
  have l64 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))]
  have l65 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l63 sK0 sK1 X0]
  have l66 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l64 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 (sK0 ◇ sK1)]
  have l67 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l65 sK0 sK1 X0]
  have l68 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l66 sK0 sK1 X0]
  have l69 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l68 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l70 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l69 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l21 (sK1 ◇ (sK0 ◇ sK1)) X0 sK0]
  have l71 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 (sK1 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1]; rw [← l70 sK0 sK1 X0]
  have l72 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l71 sK1 sK0 X0]
    conv => enter [1]; rw [l57 sK1 sK0 sK0]
  have l73 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l72 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l74 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l73 sK0 sK1 X0]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l76 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2, 2]; rw [← l67 sK1 sK0 sK0]
  have l77 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l74 sK0 sK1 X0]
    conv => enter [1]; rw [l76 sK0 sK1 X0 X1]
  have l78 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [l77 sK0 sK1 X0 X1]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2]; rw [← l75 sK1 sK0]
  have l80 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l78 sK1 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l79 sK1 sK0]
  have l81 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l80 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
  have l82 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l21 X0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l83 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
  have l84 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l83 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l85 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l81 sK1 sK0 X0 X0]
    conv => enter [1]; rw [← l82 X0 sK1 sK0]
  have l86 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l84 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l87 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X3]
    conv => enter [1]; rw [l86 X0 X1 X3 X2]
  have l88 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X3]
    conv => enter [1]; rw [l87 X0 X1 X3 X2]
  have l89 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) = ((X0 ◇ (X1 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l85 sK1 sK0 (X0 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l21 sK1 X0 X1]
  have l90 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) = (X0 ◇ ((X1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l89 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ sK1) (sK1 ◇ (X0 ◇ sK1))]
  have l91 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) = (X0 ◇ ((X1 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l90 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l88 X0 (X1 ◇ sK1) sK1 sK1]
  have l92 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l91 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 sK1 (X0 ◇ sK1)]
  have l93 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l92 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← l88 X0 X1 sK1 sK1]
  have l94 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l40 sK1 sK0 X0 X1]
    conv => enter [1]; rw [l93 sK1 sK0 X0 X1]
  have l95 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l47 sK1 sK0]
    conv => enter [1]; rw [l94 sK1 sK0 X0 X1]
  have l96 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l75 sK1 sK0]
    conv => enter [1]; rw [l95 sK0 sK1 X0 X1]
  intro x y
  conv => enter [1]; rw [l96 x y y y]

theorem Equation4512_54067_implies_Equation54057 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54057 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54067 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y]

theorem Equation4512_54067_implies_Equation54050 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54050 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l8 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54067 X0 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (X0 ◇ X0))) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X1 ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54067 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l7 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h54067 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l14 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54067 X0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l13 sK1 sK0 X0]
  have l15 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54067 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l12 sK1 sK0 X0 X0]
  have l16 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l8 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l17 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l14 X0 sK1 sK0]
    conv => enter [1]; rw [l15 X0 sK1 sK0]
  have l18 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l16 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l17 X0 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 (sK1 ◇ sK0) sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [l7 sK1 sK0 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK0 (sK1 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l30 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 sK0]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK1 ◇ sK0)]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l40 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 sK1]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l43 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l44 x y]

theorem Equation4512_54067_implies_Equation54020 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54020 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l2 sK0 X0 sK1]
    conv => enter [1]; rw [l4 sK0 X0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_54067_implies_Equation54013 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54013 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54067 X0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ X0)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l9 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l4 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 (sK1 ◇ sK0) sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK1 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l23 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54067 X0 (X0 ◇ X0) sK0]
    conv => enter [1]; rw [l7 (X0 ◇ X0) sK0 sK1]
  have l24 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l7 (X0 ◇ X1) sK0 sK1]
  have l25 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l24 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54067 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (X0 ◇ X0)]
    conv => enter [1]; rw [← l23 X0 sK0 sK1]
  have l27 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l25 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 X1 X0 X0]
  have l28 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l26 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l29 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l27 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l9 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l28 X0 sK0 sK1]
    conv => enter [1]; rw [← h54067 X0 X0 X0]
  have l31 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ X1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 2]; rw [l11 X1 sK0 X0]
    conv => enter [1]; rw [l29 X0 X1 sK0 sK1]
  have l32 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l9 X1 X0 sK0]
    conv => enter [1]; rw [l31 X0 X1 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l33 sK0 sK1 X0]
    conv => enter [1]; rw [l32 sK0 sK1 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l30 sK0 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 sK0 X0]
  have l36 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1 X0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l38 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l36 sK0 sK1 sK0]
  have l39 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X1 ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l9 (X0 ◇ sK0) X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l36 sK0 sK1 X0]
  have l40 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l39 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l41 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l9 sK0 X0 sK1]
    conv => enter [1]; rw [l38 sK0 X0 sK1]
  have l42 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ (X1 ◇ (X0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 sK0 (X1 ◇ (X0 ◇ sK0))]
    conv => enter [1]; rw [l40 X0 sK0 X1 sK1]
  have l43 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ (X1 ◇ (X0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l42 X0 sK0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← l41 sK0 sK0 sK1]
  have l44 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (X1 ◇ (X0 ◇ sK0)))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2]; rw [l41 X0 sK0 sK1]
    conv => enter [1]; rw [← l43 X0 sK0 X1 sK1]
  have l45 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ (X1 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 2]; rw [l11 sK0 X1 X0]
    conv => enter [1]; rw [← l44 X1 X0 sK0 sK1]
  have l46 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [l45 X0 sK0 X1 sK1]
  have l47 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← l9 sK0 X0 sK1]
    conv => enter [1]; rw [l46 sK0 X0 X1 sK1]
  have l48 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l9 sK0 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l37 sK0 sK1]
  have l49 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l48 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l41 sK0 sK0 sK1]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l47 sK0 sK0 sK1 X0]
    conv => enter [1]; rw [← l49 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l50 x y y]

theorem Equation4512_54067_implies_Equation54023 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54023 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54067 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54067 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54067 X0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X0)]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l6 X0 sK1 sK0]
    conv => enter [1]; rw [← h54067 X0 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l9 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l2 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54067 (sK1 ◇ sK0) sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK1 sK0 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l17 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l23 sK0 sK1 X0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 sK0 X0 sK1]
  have l27 : ∀ sK0 X1 X0 sK1 : G, (sK0 ◇ (X1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [l9 sK0 X1 X0]
    conv => enter [1, 2]; rw [l9 sK0 X0 sK1]
  have l28 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l27 sK0 X1 X0 sK1]
    conv => enter [1]; rw [l9 sK0 X1 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [l26 sK1 sK0 X0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l28 sK1 sK1 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 sK1]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 (sK0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1 sK1]
  have l35 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l28 X0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1 X0]
  have l36 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l35 X0 sK0 sK1]
    conv => enter [1]; rw [l28 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK1]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l38 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l36 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l42 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l36 X0 sK0 sK1]
  have l43 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l9 sK0 X0 sK1]
    conv => enter [1]; rw [l11 sK0 X0 sK1]
  have l44 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1]; rw [l43 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l44 x y y]

theorem Equation4512_54067_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53828 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h54067 X0 X2 X1]
    conv => enter [1]; rw [← l6 X0 X1 X2 X1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l4 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [← l12 X0 X1 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l17 sK0]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l19 sK0]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l8 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0 X1]
  have l23 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l16 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK2 sK0]
  have l25 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54067 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l26 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l28 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [← l27 sK2 sK0 X0]
  have l29 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l28 sK2 sK0 sK2]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) (sK2 ◇ sK0) sK2]
  have l30 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l29 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54067 sK0 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l30 sK2 sK0]
  have l32 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l31 sK0 sK2]
    conv => enter [1]; rw [← l22 (sK2 ◇ sK0) sK0 sK0]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l32 sK0 sK2]
    conv => enter [1]; rw [← l24 sK2 sK0]
  have l34 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 sK2]
  have l35 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l34 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l35 sK0 sK2]
  have l37 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l21 sK0]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l22 X0 sK0 X0]
    conv => enter [1]; rw [← l37 sK0 X0 X0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l38 X0 sK0]
  have l40 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l39 sK0 X0]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1, 2]; rw [l36 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l41 x y z]

theorem Equation4512_54067_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53846 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54067 (X0 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h54067 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54067 X0 X1 X2]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54067 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l0 X0 X2 X1]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54067 X0 X0 X0]
    conv => enter [1]; rw [← l5 X2 X0 X1]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X3]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h54067 X0 X1 X0]
    conv => enter [1]; rw [← l7 X0 X1 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l9 X2 (X0 ◇ X1)]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← h54067 X0 X1 X2]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l13 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1]; rw [l13 X0 X1 X2]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l14 X0 X1 X2]
  have l16 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l10 X0 X1 X1]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l11 X2 X0 X0]
    conv => enter [1]; rw [← l16 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l17 x y y]
  conv => enter [1]; rw [← l15 y z x]

theorem Equation4512_54067_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53818 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l1 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← l7 X0 X1 X2]
  have l9 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l21 X0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l25 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [l24 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation4512_54067_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53825 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54067 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4512_54067_implies_Equation53842 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53842 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l1 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l9 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l21 X0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h54067 sK0 X0 X1]
    conv => enter [1]; rw [l5 sK0 X0]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← l24 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation4512_54067_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53809 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l1 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l9 : ∀ X0 X1 sK0 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l5 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l11 sK0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l19 X0 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l21 X0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [l24 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation4512_54067_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53812 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54067 X0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 sK0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l6 X0 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54067 sK0 X0 sK1]
    conv => enter [1]; rw [l9 sK0 X0]
  have l17 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l16 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x x y]

theorem Equation4512_54067_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53832 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [l3 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54067 sK0 X0 sK1]
    conv => enter [1]; rw [l9 sK0 X0]
  have l17 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l16 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y y]

theorem Equation4512_54067_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53815 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l10 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l5 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (X2 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h54067 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54067 sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ ((X0 ◇ X1) ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h54067 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54067 sK0 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← l15 sK0 X0 X1 X2]
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1)]
  have l19 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [← l13 sK0 X2 X0 X1]
    conv => enter [1]; rw [l9 sK0 X2]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l21 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l23 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l19 X0 X1 X0 sK0]
    conv => enter [1]; rw [l21 X0 X1 X0 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l27 sK0]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l23 X0 sK0 X0]
    conv => enter [1]; rw [← l28 sK0 X0 X0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l29 X0 sK0]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l30 sK0 X0]
  have l32 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l9 sK0 X0]
    conv => enter [1]; rw [l12 sK0 X0 sK1]
  have l33 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [l32 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l33 x y y]

theorem Equation4512_54067_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53835 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54067 (X0 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h54067 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54067 X0 X1 X2]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54067 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l0 X0 X2 X1]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54067 X0 X0 X0]
    conv => enter [1]; rw [← l5 X2 X0 X1]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X3]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h54067 X0 X1 X0]
    conv => enter [1]; rw [← l7 X0 X1 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l9 X2 (X0 ◇ X1)]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← h54067 X0 X1 X2]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l10 X0 X1 X1]
    conv => enter [1]; rw [← l8 X1 X2 X0 X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l11 X2 X0 X0]
    conv => enter [1]; rw [l12 X2 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y y]

theorem Equation4512_54067_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53822 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_54067_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l8 sK0]
  have l10 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l2 sK0 (X0 ◇ X0)]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54067 X0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l15 X0 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 sK0]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l19 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l26 sK0 X0]
    conv => enter [1]; rw [← h54067 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l28 X0 sK0]
  intro x
  conv => enter [1]; rw [l29 x x]

theorem Equation4512_54133_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0]
  have l18 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l24 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation4512_54133_implies_Equation54018 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54018 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1) sK0 sK1]
  have l4 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h54133 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l2 X0 X0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0 sK1]
  have l6 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [l4 X1 X2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK0 X0 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l7 sK1 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK1 X0]
    conv => enter [1, 2]; rw [← l9 sK1 sK1]
  have l12 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK1 sK0 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK1 sK1 sK1]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [← l11 sK1 sK1]
  have l16 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
    conv => enter [1]; rw [l15 sK1]
  have l17 : ∀ X1 X2 X0 sK0 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X2 X0 sK0 sK2
    conv => enter [1]; rw [h54133 X1 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK2 X1]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l2 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK0 X0 sK0 sK2]
  have l19 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 X0 sK2]
  have l20 : ∀ sK1 X0 sK0 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l19 sK0 sK1 X0 sK2]
  have l21 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l16 sK0 sK2 sK0]
    conv => enter [1]; rw [l20 sK0 X0 sK0 sK2]
  have l22 : ∀ sK0 sK2 X1 X2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK0 sK2 X1 X2
    conv => enter [1]; rw [l21 sK0 sK2 sK0]
    conv => enter [1]; rw [← l17 X1 X2 sK0 sK0 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54133 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l23 x z y]

theorem Equation4512_54133_implies_Equation54118 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54118 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1) sK0 sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54133 sK0 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l4 X0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_54133_implies_Equation54031 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54031 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h54133 X3 X4 X2 X2]
    conv => enter [1, 2]; rw [l0 X2 X2 X0 X1]
  have l2 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X4) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ X2) X4]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X4) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ ((X1 ◇ X0) ◇ X4)) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X4]
    conv => enter [1]; rw [l3 X0 X1 X4 X2 X3]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X4))) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X0 X4]
    conv => enter [1]; rw [l4 X0 X1 X4 X2 X3]
  intro x y z
  conv => enter [1]; rw [l1 x y x y x]
  conv => enter [1]; rw [l5 x y y x z]

theorem Equation4512_54133_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54053 G := by
  have l0 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK2 ◇ sK0) ◇ X0)]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l0 sK1 sK0 sK2 X0]
  have l2 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h54133 X3 X4 X2 X2]
    conv => enter [1, 2]; rw [h54133 X2 X2 X0 X1]
  have l3 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l4 : ∀ X1 X2 X0 sK0 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X1 X2 X0 sK0 sK2
    conv => enter [1]; rw [h54133 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l3 X0 X0 sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 X0 sK0 sK2]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l3 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l7 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [l2 X0 X1 X2 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
  have l8 : ∀ X0 X1 X2 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 X2 sK1 sK0 sK2
    conv => enter [1]; rw [l7 X0 X1 X2 sK1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l9 : ∀ sK0 sK2 X2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X2 sK1 sK0 sK2]
  have l10 : ∀ sK0 sK1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 X2 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK2 X2 sK1]
  have l11 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l10 sK0 sK1 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l12 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
    conv => enter [1]; rw [← l11 sK1 sK0 sK2]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l13 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_54133_implies_Equation54027 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54027 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l4 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l2 X0 X1 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK1 sK2 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l4 X0 X1 X2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0 sK0]
    conv => enter [1, 1]; rw [l2 sK1 sK0 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_54133_implies_Equation54071 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54071 G := by
  have l0 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h54133 X3 X4 X2 X2]
    conv => enter [1, 2]; rw [h54133 X2 X2 X0 X1]
  have l1 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l2 : ∀ X0 X1 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro X0 X1 sK2 sK1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK2]
  have l3 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h54133 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l1 X0 X0 sK0 sK1]
  have l4 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l1 X0 X1 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) sK2]
  have l6 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l4 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 sK0 sK1]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l9 : ∀ X2 X3 X4 X5 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X4 ◇ (X5 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X2 X3 X4 X5 X0 X1
    conv => enter [1]; rw [l0 X2 X3 X4 X5 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l10 : ∀ X2 X3 X4 X5 sK0 sK1 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X4 ◇ (X5 ◇ (X5 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)))) := by
    intro X2 X3 X4 X5 sK0 sK1 X1
    conv => enter [1]; rw [l9 X2 X3 X4 X5 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 sK1 X1 X2 X1]
  have l11 : ∀ X2 X3 X4 X5 sK0 sK1 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X4 ◇ (X5 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro X2 X3 X4 X5 sK0 sK1 X1
    conv => enter [1]; rw [l10 X2 X3 X4 X5 sK0 sK1 X1]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 X1 X5]
  have l12 : ∀ X2 X3 X4 sK0 sK1 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X4 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro X2 X3 X4 sK0 sK1 X1
    conv => enter [1]; rw [l11 X2 X3 X4 X2 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 X1 X2]
  have l13 : ∀ sK2 sK1 sK0 X4 X1 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK2) = (X4 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK2 sK1 sK0 X4 X1
    conv => enter [1]; rw [← l2 sK2 sK2 sK2 sK1 sK0]
    conv => enter [1]; rw [l12 sK2 sK2 X4 sK0 sK1 X1]
  have l14 : ∀ sK0 sK1 X4 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X4 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 sK1 X4 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK0 X4 X1]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l14 sK0 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1 X0]
  have l18 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l17 sK0 sK1 X2]
    conv => enter [1]; rw [← l4 X0 X1 X2 sK0 sK1]
  have l19 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l19 x y y z x]

theorem Equation4512_54133_implies_Equation54026 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54026 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X4 ◇ X4))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [← h54133 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X2 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X2 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y y z]

theorem Equation4512_54133_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54034 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X4 ◇ X4))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [← h54133 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 X2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_54133_implies_Equation54022 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54022 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK2 X0]
  have l2 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l3 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X4 ◇ X4))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [← h54133 X2 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l2 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ X2 X0 X1 sK0 sK1 sK2 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X2 X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l4 X2 X2 X2 X0 X1]
    conv => enter [1]; rw [l5 X2 X2 sK0 sK1 sK2]
  have l7 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h54133 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l2 X0 X0 sK0 sK1]
  have l8 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l2 X0 X1 sK0 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l8 X0 X1 X2 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 X0 sK0 sK1]
  have l12 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l13 : ∀ X2 X0 X1 X3 X4 X5 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X3 ◇ (X4 ◇ (X5 ◇ X3))) := by
    intro X2 X0 X1 X3 X4 X5
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X2 (X0 ◇ X1) X3 X4 X5]
  have l14 : ∀ X2 X0 X1 sK0 sK1 sK2 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X2 X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l13 X2 X0 X1 X2 X2 X2]
    conv => enter [1]; rw [l6 X2 X2 X2 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l14 X2 X0 X1 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 X2 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK0 sK1 X2 X1
    conv => enter [1]; rw [l15 sK0 sK1 X2 sK0 X1]
    conv => enter [1, 2, 2]; rw [l10 sK0 X1 X1 sK0 sK1]
  have l17 : ∀ sK0 sK1 X2 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 sK1 X2 X1
    conv => enter [1]; rw [l16 sK0 sK1 X2 X1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1 X1 X2]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l17 sK0 sK1 (sK1 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l18 sK0 sK1 sK0 X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation4512_54133_implies_Equation54088 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54088 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l2 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

end Semigroup5
