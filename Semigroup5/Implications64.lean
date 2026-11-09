import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54075_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation54053 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK2 ◇ sK0) ◇ X0)]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l1 sK1 sK0 sK2 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l7 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l8 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 X0]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54075 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l13 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l14 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h54075 (sK2 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK0)]
  have l15 : ∀ sK2 sK0 X0 X1 sK1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0))) = (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro sK2 sK0 X0 X1 sK1
    conv => enter [1]; rw [h54075 ((sK2 ◇ sK0) ◇ X0) X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK1 sK0 sK2 X0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l9 sK1 sK0]
  have l17 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54075 (X1 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h54075 X0 X1 X1]
  have l18 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 X0]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54075 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X2 ◇ X3))]
  have l20 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54075 X0 X1 X2]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK0 (sK1 ◇ sK0)]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK1 sK0]
  have l23 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54075 X0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)]
  have l24 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK2 sK0]
  have l25 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK0 sK2 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 (sK1 ◇ sK0) (sK2 ◇ sK0)]
  have l26 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l27 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l20 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l17 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l29 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK1 sK0 (sK1 ◇ sK0)]
  have l30 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0)))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l15 sK2 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) X0 (X1 ◇ ((sK2 ◇ sK0) ◇ X0))]
  have l31 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [← l13 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ X0))]
  have l32 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l12 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l33 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l34 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l27 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l35 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l29 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l26 sK1 sK0 (sK1 ◇ sK0)]
  have l36 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0))) = (X1 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l30 X1 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l28 X1 X0 (sK2 ◇ sK0)]
  have l37 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) = (X1 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l31 X1 sK1 sK0 X0]
    conv => enter [1]; rw [← l28 X1 X0 sK0]
  have l38 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l32 X0 sK0 sK1]
    conv => enter [1]; rw [← l28 X0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l39 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l33 sK0 X0 sK1]
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l34 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l41 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l35 sK1 sK0 X0]
  have l42 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l38 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l43 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l39 sK0 X0 sK1]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) sK1 sK0]
  have l44 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l40 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l45 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l41 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l46 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l43 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l47 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l45 sK1 sK0 X0]
    conv => enter [1]; rw [← l28 X0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l46 sK0 sK1 sK1]
  have l49 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l47 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK1 sK0]
    conv => enter [1]; rw [l50 sK1 sK0]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l50 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l50 sK1 sK0]
  have l54 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l50 sK1 sK0]
  have l55 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l54 sK1 sK0 X0]
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l58 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l55 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l57 sK1 sK0]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l58 sK0 sK1 X0]
    conv => enter [1]; rw [← l28 X0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l60 sK1 sK0]
    conv => enter [1]; rw [← l42 sK1 sK0 sK1]
  have l63 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l64 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l62 sK1 sK0]
  have l65 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l49 sK1 sK0 X0]
    conv => enter [1]; rw [← l63 sK0 sK1 X0]
  have l66 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54075 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [l51 sK1 sK0]
  have l67 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l66 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))]
  have l68 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l67 X0 sK1 sK0]
    conv => enter [1]; rw [← l28 X0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l69 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l68 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l64 sK1 sK0]
  have l70 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 (sK0 ◇ (sK1 ◇ sK0)) X0 sK1 sK0]
    conv => enter [1]; rw [← l69 X0 sK1 sK0]
  have l71 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l65 sK1 sK0 X0]
    conv => enter [1]; rw [l70 sK0 sK1 X0]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l59 sK1 sK0]
  have l73 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l59 sK1 sK0]
  have l74 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l73 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l72 sK1 sK0]
  have l76 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l74 sK1 sK0 X0]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0 sK1]
    conv => enter [1]; rw [l75 sK1 sK0]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1 sK0]
    conv => enter [1]; rw [l19 (sK1 ◇ sK0) sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [l77 sK1 sK0]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [← l28 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l81 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l79 sK1 sK0]
  have l82 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← l37 (sK1 ◇ sK0) sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l83 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l82 sK0 sK1]
  have l84 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l83 sK1 sK0]
    conv => enter [1]; rw [← l65 sK1 sK0 sK0]
  have l85 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) sK0 sK0]
  have l86 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l85 sK1 sK0]
  have l87 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l51 sK1 sK0]
    conv => enter [1]; rw [l86 sK1 sK0]
  have l88 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l81 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l88 sK1 sK0]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l91 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l65 sK1 sK0 sK1]
    conv => enter [1]; rw [l90 sK0 sK1]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK1 sK0]
    conv => enter [1]; rw [l91 sK1 sK0]
  have l93 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l92 sK1 sK0]
  have l94 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l87 sK1 sK0]
  have l95 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← l87 sK1 sK0]
  have l96 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l94 sK1 sK0]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l97 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l93 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l98 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l97 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l99 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l98 sK1 sK0 X0]
  have l100 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l101 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l102 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK2 sK0]
  have l103 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l101 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l104 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l100 sK1 sK0]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l105 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l51 sK1 sK0]
    conv => enter [1]; rw [l104 sK1 sK0]
  have l106 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l93 sK1 sK0]
    conv => enter [1, 2]; rw [← l105 sK1 sK0]
  have l107 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [← l7 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l108 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l105 sK1 sK0]
  have l109 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l108 sK0 sK1 X0]
  have l110 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l107 sK2 sK1 sK0]
  have l111 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [← l110 sK0 sK1 sK2]
  have l112 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l111 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l113 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l112 sK0 sK1 sK2]
    conv => enter [1]; rw [← l65 sK1 sK0 sK2]
  have l114 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l113 sK0 sK1 sK2]
    conv => enter [1]; rw [← l102 sK2 sK0 sK1]
  have l115 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK2 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l102 sK2 sK0 sK1]
  have l116 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l115 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l117 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [← l116 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l118 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l117 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l28 X0 (sK1 ◇ sK0) sK2]
  have l119 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l118 X0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l102 sK2 sK0 sK1]
  have l120 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h54075 (sK2 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l121 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (X0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [h54075 (sK2 ◇ sK0) X0 sK0]
  have l122 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK2 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l123 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l122 sK2 sK0 sK1]
  have l124 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l122 sK2 sK0 sK1]
  have l125 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l122 sK2 sK0 sK1]
  have l126 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l125 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l127 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l123 sK0 sK1 sK2]
    conv => enter [1]; rw [← l109 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l128 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l124 sK1 sK0 sK2]
    conv => enter [1]; rw [← l127 sK0 sK1 sK2]
  have l129 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h54075 (sK2 ◇ sK0) sK0 sK0]
  have l130 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 X0]
    conv => enter [1, 2]; rw [← h54075 (sK2 ◇ sK0) sK0 sK0]
  have l131 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l130 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l132 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l129 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l122 sK2 sK0 sK1]
  have l133 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l131 sK0 X0 sK2]
    conv => enter [1]; rw [← l36 sK0 sK1 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
  have l134 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l120 sK2 sK0 sK1]
    conv => enter [1]; rw [l132 sK1 sK0 sK2]
  have l135 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l133 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l136 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l44 sK0 sK0 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [l135 sK0 sK0 sK2 sK1]
  have l137 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l136 sK0 sK2 sK1]
    conv => enter [1]; rw [← l121 sK0 sK2 sK0]
  have l138 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l124 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l139 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l99 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l138 sK1 sK0 sK2]
  have l140 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l124 sK1 sK0 sK2]
    conv => enter [1]; rw [l139 sK1 sK0 sK2]
  have l141 : ∀ sK2 sK0 sK1 X0 : G, (((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l134 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
  have l142 : ∀ sK2 sK0 sK1 X0 : G, (((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l141 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l143 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [l142 sK2 sK0 sK1 X0]
  have l144 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l140 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l145 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l140 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l146 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l145 sK0 sK1 sK2]
    conv => enter [1]; rw [l137 sK0 sK1 sK2]
  have l147 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l144 sK1 sK0 sK2]
    conv => enter [1]; rw [← l143 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l148 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l140 sK1 sK0 sK2]
    conv => enter [1]; rw [l147 sK1 sK0 sK2]
  have l149 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l128 sK1 sK0 sK2]
    conv => enter [1]; rw [l146 sK0 sK1 sK2]
  have l150 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l148 sK1 sK0 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l151 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK2 ◇ sK0)) sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l150 sK0 sK1 sK2]
  have l152 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l151 sK0 sK2 sK0]
    conv => enter [1]; rw [l137 sK0 sK0 sK2]
  have l153 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l152 sK0 sK2]
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK1]
  have l154 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l153 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l155 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l153 sK0 sK2 sK1]
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) sK0 X0]
  have l156 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l155 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l44 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l157 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l154 sK1 sK0 sK2]
  have l158 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l156 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l159 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l149 sK1 sK0 sK2]
    conv => enter [1]; rw [l157 sK1 sK0 sK2]
  have l160 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l158 sK1 sK0 sK2]
  have l161 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l159 sK0 sK2 sK1]
    conv => enter [1]; rw [← l160 sK1 sK0 sK2]
  have l162 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l161 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l23 (sK0 ◇ (sK2 ◇ sK0)) sK1 sK0 sK2]
  have l163 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l162 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l164 : ∀ sK0 sK2 X0 sK1 : G, (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l163 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l165 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l164 sK0 sK2 X0 sK1]
  have l166 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54075 sK0 sK0 sK1]
  have l167 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54075 sK0 sK0 sK1]
  have l168 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) sK1 sK0]
  have l169 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54075 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l170 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l169 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l171 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l168 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l172 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l167 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l173 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l166 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l174 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l170 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [h54075 (sK1 ◇ sK0) sK1 sK0]
  have l175 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l171 sK0 sK1]
  have l176 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK1 sK0 sK0]
    conv => enter [1]; rw [← l172 sK1 sK0]
  have l177 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l24 sK2 sK0 sK0]
    conv => enter [1]; rw [← l173 sK2 sK0 sK1]
  have l178 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l103 (sK2 ◇ sK0) sK1 sK0 sK1]
    conv => enter [1]; rw [← l174 sK2 sK0 sK1]
  have l179 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l176 sK0 sK1]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) sK1 sK0]
  have l180 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l177 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54075 sK0 (sK2 ◇ sK0) sK0]
  have l181 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l175 sK0 sK1]
    conv => enter [1]; rw [← l178 sK1 sK0 sK2]
  have l182 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l179 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l183 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l180 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l184 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l181 sK2 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 sK2 (sK1 ◇ (sK1 ◇ sK0))]
  have l185 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l184 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54075 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l186 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l185 sK2 sK0 sK1]
  have l187 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l186 sK0 sK1 sK2]
  have l188 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l114 sK0 sK1 sK2]
    conv => enter [1]; rw [l187 sK0 sK1 sK2]
  have l189 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [l106 sK1 sK0]
    conv => enter [1, 2]; rw [← l182 sK0 sK1]
  have l190 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [l96 sK1 sK0]
  have l191 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l192 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l193 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l190 sK1 sK0]
    conv => enter [1]; rw [← l191 sK0 sK1]
  have l194 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l189 sK0 sK1]
    conv => enter [1]; rw [l193 sK1 sK0]
  have l195 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l183 sK0 sK2]
    conv => enter [1]; rw [← l8 sK2 sK0 sK0]
  have l196 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l183 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l197 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l195 sK2 sK0]
  have l198 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l196 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 X0]
  have l199 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← l175 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l200 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l199 sK1 sK0 X0]
  have l201 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l192 sK0 sK1 X0]
    conv => enter [1]; rw [l200 sK1 sK0 X0]
  have l202 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l196 sK1 sK0 sK2]
    conv => enter [1]; rw [← l188 sK2 sK0 sK1]
  have l203 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)))) = (((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h54075 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← l188 sK2 sK0 sK1]
  have l204 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l203 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l205 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l198 sK1 sK0 sK2 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l204 sK0 X0 sK1 sK2]
  have l206 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l205 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l44 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 sK0 sK1]
  have l207 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l206 sK1 sK0 sK2]
    conv => enter [1]; rw [← l198 sK1 sK0 sK2 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0)]
  have l208 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l207 sK1 sK0 sK2]
    conv => enter [1]; rw [← l165 sK0 sK2 sK0 sK1]
  have l209 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l208 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l183 sK0 sK2]
  have l210 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l25 sK1 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l209 sK1 sK0 sK2]
  have l211 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l21 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l210 sK0 sK1 sK2]
  have l212 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l201 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l211 sK0 sK1 sK2]
  have l213 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l105 sK1 sK0]
    conv => enter [1]; rw [l212 sK0 sK1 sK2]
  have l214 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [l213 sK1 sK0 sK2]
  have l215 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l214 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
  have l216 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l189 sK0 sK1]
    conv => enter [1]; rw [l215 sK1 sK0 sK2]
  have l217 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l216 sK0 sK1 sK2]
    conv => enter [1]; rw [l148 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l216 sK0 sK1 sK2]
  have l218 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l217 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l219 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l194 sK0 sK1]
    conv => enter [1]; rw [l218 sK0 sK1 sK2]
  have l220 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l202 sK0 sK1 sK2]
  have l221 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l220 sK0 sK1 sK2]
    conv => enter [1]; rw [← l201 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l222 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l119 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [l221 sK0 sK1 sK2]
  have l223 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l222 sK0 sK2 sK1]
  have l224 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l219 sK0 sK1 sK2]
    conv => enter [1]; rw [l223 sK0 sK2 sK1]
  have l225 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l224 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l226 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h54075 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK1]
  have l227 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l226 sK2 sK0 sK2]
    conv => enter [1]; rw [← l153 sK0 sK2 sK2]
  have l228 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l214 sK0 sK1 sK2]
    conv => enter [1]; rw [← l227 sK2 sK0]
  have l229 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l228 sK0 sK1 sK2]
    conv => enter [1]; rw [l126 sK2 sK0 (sK2 ◇ sK0) sK1]
  have l230 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l229 sK0 sK1 sK2]
    conv => enter [1]; rw [← l225 sK0 sK1 (sK2 ◇ sK0) sK2]
  have l231 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h54075 (sK2 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l230 sK0 sK1 sK2]
  have l232 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l231 sK2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l105 sK1 sK0]
  have l233 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l182 sK0 sK1]
    conv => enter [1]; rw [← l232 sK2 sK0 X0 sK1]
  have l234 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = (((sK2 ◇ sK0) ◇ sK0) ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1, 2, 2]; rw [l197 sK2 sK0]
    conv => enter [1]; rw [← h54075 ((sK2 ◇ sK0) ◇ sK0) X0 (sK2 ◇ sK0)]
  have l235 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l234 X0 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) sK0 (X0 ◇ ((sK2 ◇ sK0) ◇ sK0))]
  have l236 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l235 X0 sK2 sK0]
    conv => enter [1]; rw [← l28 X0 sK0 (sK2 ◇ sK0)]
  have l237 : ∀ X0 sK2 sK0 : G, (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l236 X0 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l238 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l183 sK0 sK2]
    conv => enter [1]; rw [← l237 X0 sK2 sK0]
  have l239 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l238 X0 sK0 sK2]
    conv => enter [1]; rw [← h54075 (sK2 ◇ sK0) X0 (sK2 ◇ sK0)]
  have l240 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l239 X0 sK0 sK2]
    conv => enter [1]; rw [← l233 X0 sK0 sK1 sK2]
  have l241 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l189 sK0 sK1]
    conv => enter [1]; rw [l240 sK1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l241 x y z]

theorem Equation4512_54075_implies_Equation4269 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation4269 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
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
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l10 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l8 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l7 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l16 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ sK0) sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l8 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h54075 sK0 sK0 sK0]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l21 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l27 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK0 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h54075 sK0 sK1 sK0]
  have l33 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l32 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l34 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 sK0]
    conv => enter [1]; rw [l33 sK0 X0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ sK0)]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [h54075 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l24 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l40 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK0 sK0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l41 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK1 ◇ sK0)]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l28 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l47 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l30 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1, 2]; rw [← l31 sK0 sK1]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l54 sK1 sK0]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l58 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
  have l59 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [l58 X0 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l63 sK0 sK1]
  have l67 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l66 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l55 sK1 sK0]
  have l68 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l34 X0 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1 X0]
  have l69 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l59 X0 sK0 sK1]
    conv => enter [1]; rw [← l68 X0 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l69 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l70 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l71 x y]

theorem Equation4512_54075_implies_Equation54071 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation54071 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54075 X0 X2 X0]
    conv => enter [1, 2]; rw [h54075 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54075 (X0 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h54075 X2 (X0 ◇ X2) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54075 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ X0))]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X2 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← h54075 (X0 ◇ X0) X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [l3 X1 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X1 X1 X0]
    conv => enter [1]; rw [l4 X1 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l11 X0 X0 X1]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← h54075 X0 X1 X2]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l14 X0 X1 X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l16 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [← l13 y y x]
  conv => enter [1]; rw [← l17 y z x]

theorem Equation4512_54075_implies_Equation54026 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation54026 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54075 X0 X2 X0]
    conv => enter [1, 2]; rw [h54075 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54075 (X0 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h54075 X2 (X0 ◇ X2) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54075 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ X0))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X2 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← h54075 (X0 ◇ X0) X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X1 X1]
    conv => enter [1]; rw [l4 X1 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l11 X0 X0 X1]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l12 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [← l13 x y z]

theorem Equation4512_54075_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation54034 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X3 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54075 X2 X0 X1]
    conv => enter [1]; rw [h54075 X2 X0 X3]
  have l3 : ∀ X0 X2 X3 X1 : G, ((X0 ◇ X2) ◇ (X3 ◇ (X0 ◇ X2))) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h54075 (X0 ◇ X2) X3 X2]
    conv => enter [1, 2, 2]; rw [h54075 X2 X0 X1]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54075 ((sK1 ◇ sK0) ◇ X0) X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54075 X0 X2 X0]
    conv => enter [1, 2]; rw [h54075 X0 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54075 (X1 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h54075 X0 X1 X1]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54075 X0 X1 X2]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK1 sK0]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l6 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l11 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) X0 (X1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l12 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X0 X2 (X3 ◇ (X0 ◇ X2))]
  have l13 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l9 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l14 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l11 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 X1 X0 (sK1 ◇ sK0)]
  have l15 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l12 X3 X2 X0 X1]
    conv => enter [1]; rw [← l10 X3 X2 X0]
  have l16 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l13 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l16 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l18 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [h54075 (sK2 ◇ (sK1 ◇ sK0)) X0 sK0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h54075 sK0 sK1 sK1]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54075 sK0 sK0 sK1]
  have l21 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54075 sK0 (sK1 ◇ sK0) sK1]
  have l22 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l21 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54075 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l22 sK2 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK1 sK0 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l26 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0 (sK1 ◇ sK0)]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) sK0 sK2]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 sK0]
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK0 sK0]
  have l30 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l32 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l30 sK2 sK0 sK1]
  have l33 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l32 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l31 sK0 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l34 sK0 sK1 X0]
  have l36 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l19 sK1 sK0 X0]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) X0 sK0]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l19 sK1 sK0 X0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l19 sK1 sK0 sK1]
    conv => enter [1]; rw [← h54075 sK0 (sK1 ◇ sK0) sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 sK0 sK0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l43 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l45 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l36 X0 sK0 sK1]
    conv => enter [1]; rw [l43 X0 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l48 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l47 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l50 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l52 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l19 sK1 sK0 sK2]
    conv => enter [1]; rw [← l48 sK2 sK1 sK0]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l54 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l19 sK1 sK0 sK2]
    conv => enter [1]; rw [l30 sK2 sK0 sK1]
  have l55 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK0 sK2]
  have l56 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l19 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l57 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l56 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [l33 sK2 sK0 sK1 X0]
  have l58 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l55 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
  have l59 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l57 sK1 sK0 sK2 X0]
  have l60 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l45 X0 sK0 sK1]
    conv => enter [1]; rw [l58 sK0 sK1 X0 sK2]
  have l61 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK0]
  have l62 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l63 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l62 sK1 sK0 X0]
  have l64 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l61 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l37 sK0 sK1 (sK1 ◇ sK0)]
  have l65 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 X0]
    conv => enter [1]; rw [l63 sK1 sK0 X0]
  have l66 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l64 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l67 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 X0 sK1]
  have l68 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l36 X0 sK0 sK1]
    conv => enter [1]; rw [l67 X0 sK0 sK1]
  have l69 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l54 sK1 sK0 sK2]
  have l70 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l54 sK1 sK0 sK2]
  have l71 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l70 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l14 X0 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l72 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l69 sK0 sK2 sK1]
  have l73 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l71 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l44 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l74 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l45 X0 sK0 sK1]
    conv => enter [1]; rw [l73 sK0 sK1 X0 sK2]
  have l75 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK2 ◇ (sK1 ◇ sK0)) X0 sK2]
    conv => enter [1, 2]; rw [← h54075 (sK1 ◇ sK0) sK2 sK2]
  have l76 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l75 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l19 sK1 sK0 sK2]
  have l77 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l76 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l30 sK2 sK0 sK1]
  have l78 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l77 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l54 sK1 sK0 sK2]
  have l79 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l72 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l80 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l79 sK0 sK1 sK2 X0]
  have l81 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l19 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l52 sK1 sK0 sK2]
  have l82 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l81 sK2 sK1 sK0]
  have l83 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l54 sK1 sK0 sK2]
    conv => enter [1]; rw [← l82 sK0 sK1 sK2]
  have l84 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l83 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK2 ◇ (sK1 ◇ sK0))]
  have l85 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK2 ◇ (sK1 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l83 sK1 sK0 sK2]
  have l86 : ∀ sK1 sK0 sK2 X0 : G, (((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l83 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l87 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l86 sK1 sK0 sK2 X0]
  have l88 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l85 sK2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l53 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l89 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l84 sK1 sK0 sK2]
    conv => enter [1]; rw [← l50 sK0 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l90 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l74 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l88 sK2 sK1 sK0 X0]
  have l91 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l83 sK1 sK0 sK2]
    conv => enter [1]; rw [← l89 sK1 sK0 sK2]
  have l92 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l91 sK1 sK0 sK2]
    conv => enter [1]; rw [← l78 sK2 sK1 sK0 sK1]
  have l93 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l90 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l92 sK1 sK0 sK2]
  have l94 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l93 sK1 sK0 sK2]
  have l95 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [l94 sK1 sK0 sK2]
  have l96 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0))]
  have l97 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l98 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l30 sK2 sK0 sK1]
    conv => enter [1]; rw [l96 sK2 sK0 sK1]
  have l99 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l54 sK1 sK0 sK2]
    conv => enter [1]; rw [l98 sK2 sK1 sK0]
  have l100 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l95 sK0 sK1 sK2]
    conv => enter [1]; rw [l99 sK1 sK0 sK2]
  have l101 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l100 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l102 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l26 sK0 sK2 sK1]
  have l103 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l102 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l104 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l103 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l105 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l104 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l33 sK2 sK0 sK1 (sK0 ◇ X0)]
  have l106 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l105 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l59 sK1 sK0 sK2 (sK0 ◇ X0)]
  have l107 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l97 sK0 sK1 (sK0 ◇ X0) sK2]
    conv => enter [1]; rw [← l106 sK0 sK2 sK1 X0]
  have l108 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l65 sK0 sK1 X0]
    conv => enter [1]; rw [l107 sK0 sK1 X0 sK2]
  have l109 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h54075 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1]; rw [← l108 sK0 sK1 (sK0 ◇ X0) sK2]
  have l110 : ∀ sK0 X0 X1 sK2 sK1 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) = (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1 sK2 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ X0) X1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l108 sK0 sK1 X0 sK2]
  have l111 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l110 sK0 X0 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← l80 sK0 sK1 sK2 X0]
  have l112 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l65 sK0 sK1 X0]
    conv => enter [1]; rw [← l109 X0 sK0 sK2 sK1]
  have l113 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) = (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l111 sK0 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l87 sK1 sK0 sK2 X0]
  have l114 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [l97 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l113 sK0 X0 X1 sK1 X1]
  have l115 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l114 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ X0))]
  have l116 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l115 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 X1 X0 sK0]
  have l117 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l45 X0 sK0 sK1]
  have l118 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l117 sK1 sK0 X0]
  have l119 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l45 X0 sK0 sK1]
    conv => enter [1]; rw [l118 sK0 sK1 X0]
  have l120 : ∀ X0 X1 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = (((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK2 sK1 sK0
    conv => enter [1]; rw [← h54075 ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2]; rw [← l60 X0 sK0 sK1 sK2]
  have l121 : ∀ X0 X1 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK2 sK1 sK0
    conv => enter [1]; rw [l120 X0 X1 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l122 : ∀ sK0 sK1 X0 X1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [l101 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1]; rw [← l121 X0 X1 sK2 sK1 sK0]
  have l123 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l122 sK0 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [← l17 (sK2 ◇ (sK1 ◇ sK0)) X0 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l124 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l123 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← l60 X0 sK0 sK1 sK2]
  have l125 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l45 X0 sK0 sK1]
    conv => enter [1]; rw [l124 sK0 sK1 X0 sK2]
  have l126 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l65 sK0 sK1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54075 X0 sK0 X1]
  have l127 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l116 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1 X0]
    conv => enter [1]; rw [← l126 sK0 sK1 X1 X0]
  have l128 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l35 sK0 sK1 X0]
    conv => enter [1]; rw [l127 sK0 sK1 X0 X1]
  have l129 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l44 sK0 sK1 X0]
    conv => enter [1]; rw [l128 sK0 sK1 X0 X1]
  have l130 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l68 X0 sK0 sK1]
    conv => enter [1]; rw [← l65 sK0 sK1 (X0 ◇ sK0)]
  have l131 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l45 X0 sK0 sK1]
    conv => enter [1]; rw [l130 sK0 sK1 X0]
  have l132 : ∀ X1 X0 sK2 sK1 sK0 X2 : G, (X1 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = (X1 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))))) := by
    intro X1 X0 sK2 sK1 sK0 X2
    conv => enter [1, 2, 2]; rw [h54075 (sK2 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1]; rw [l2 X1 X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) X2]
  have l133 : ∀ sK0 sK1 X2 X1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ (X2 ◇ X1))) = ((X2 ◇ (X2 ◇ X1)) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X2 X1 sK2 X0
    conv => enter [1]; rw [l112 sK0 sK1 (X2 ◇ (X2 ◇ X1)) sK2]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X2 X1 X0]
  have l134 : ∀ sK0 sK1 X2 X1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ (X2 ◇ X1))) = (X2 ◇ ((X2 ◇ X1) ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro sK0 sK1 X2 X1 sK2 X0
    conv => enter [1]; rw [l133 sK0 sK1 X2 X1 sK2 X0]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ X1) ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l135 : ∀ X1 X0 sK2 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) := by
    intro X1 X0 sK2 sK1 sK0
    conv => enter [1]; rw [l132 X1 X0 sK2 sK1 sK0 X1]
    conv => enter [1]; rw [← l17 sK0 X1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) X1]
  have l136 : ∀ sK0 sK1 X2 X1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ (X2 ◇ X1))) = (X2 ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro sK0 sK1 X2 X1 sK2 X0
    conv => enter [1]; rw [l134 sK0 sK1 X2 X1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l137 : ∀ X1 X0 sK2 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X0 sK2 sK1 sK0
    conv => enter [1]; rw [l135 X1 X0 sK2 sK1 sK0]
    conv => enter [1]; rw [← l18 sK0 sK2 sK1 X1]
  have l138 : ∀ sK0 sK1 X2 X1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ (X2 ◇ X1))) = (X2 ◇ (X2 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ X1)))) := by
    intro sK0 sK1 X2 X1 sK2
    conv => enter [1]; rw [l136 sK0 sK1 X2 X1 sK2 sK0]
    conv => enter [1, 2]; rw [l15 X2 X1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
  have l139 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l90 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l137 X1 X0 sK2 sK1 sK0]
  have l140 : ∀ sK0 sK1 X2 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ (X2 ◇ X1))) = (X2 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK0 sK1 X2 X1
    conv => enter [1]; rw [l138 sK0 sK1 X2 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l112 sK0 sK1 X1 sK0]
  have l141 : ∀ sK0 sK1 X1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X1 sK0]
    conv => enter [1]; rw [l139 X1 sK0 sK0 sK1 sK2]
  have l142 : ∀ sK0 sK1 X1 X2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (X2 ◇ (X2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l129 sK0 sK1 X1 X2]
    conv => enter [1]; rw [l140 sK0 sK1 X2 X1]
  have l143 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l45 X1 sK0 sK1]
    conv => enter [1]; rw [l141 sK0 sK1 X1 sK2]
  have l144 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l112 sK0 sK1 (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [← l143 X0 sK0 sK1 sK2]
  have l145 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1, 2]; rw [l143 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK0 sK2 (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l146 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l145 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [← l97 sK0 sK1 (X0 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK2]
  have l147 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l144 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l148 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l119 X0 sK0 sK1]
    conv => enter [1]; rw [l146 sK1 X0 sK0 sK2]
  have l149 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l125 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l147 sK0 sK1 X0 sK2]
  have l150 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l148 X0 sK0 sK1 X0]
    conv => enter [1]; rw [← l149 X0 sK0 sK1 X0]
  have l151 : ∀ X0 sK0 sK1 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 1]; rw [l150 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1]
  have l152 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1]; rw [l151 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l153 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l142 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l152 X0 sK0 sK1 X1]
  have l154 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ sK0)]
  have l155 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l154 sK0 X0 sK1]
    conv => enter [1]; rw [← l153 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0) X0]
  have l156 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l155 sK0 X0 sK1]
    conv => enter [1]; rw [← l131 (sK1 ◇ sK0) sK0 sK1]
  have l157 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l156 sK0 X0 sK1]
  have l158 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l157 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l158 x y z y]

@[equational_result]
theorem Equation54075_implies_Equation54047 (G : Type*) [Magma G] (h54075 : Equation54075 G) : Equation54047 G := by
  intro x y
  conv => enter [1]; rw [h54075 x y x]

theorem Equation4512_54075_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53828 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l8 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l8 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l13 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l6 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l16 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK0]
  have l25 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h54075 sK0 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l27 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l28 sK0]
  have l30 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l26 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l26 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l30 sK2 sK0]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l34 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK0 ◇ sK0)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h54075 sK0 sK2 sK0]
  have l35 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l36 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1]; rw [l35 sK0 X0 sK2]
  have l37 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l26 sK0]
    conv => enter [1]; rw [← h54075 (sK0 ◇ sK0) X0 sK0]
  have l38 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54075 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l39 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54075 (sK0 ◇ sK0) sK2 sK0]
  have l40 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l39 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l40 sK2 sK0]
    conv => enter [1]; rw [l5 sK0 sK2 sK0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l41 sK0]
  have l44 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l42 sK2 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [← l31 sK0 (sK0 ◇ sK0)]
  have l46 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l32 sK2 sK0]
    conv => enter [1]; rw [l44 sK2 sK0]
  have l47 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [l46 sK2 sK0]
  have l48 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l47 sK0 sK2]
    conv => enter [1]; rw [← l14 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l49 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l47 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l48 sK2 sK0]
    conv => enter [1, 2]; rw [← l32 sK2 sK0]
  have l51 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l50 sK2 sK0]
    conv => enter [1, 2]; rw [← l33 sK0 sK2]
  have l52 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l51 sK2 sK0]
  have l53 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 (sK0 ◇ sK0)]
  have l54 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ sK0)]
  have l55 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ sK0) X0]
  have l56 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l53 sK0 sK2]
    conv => enter [1]; rw [← l37 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l57 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l47 sK0 sK2]
    conv => enter [1]; rw [← l56 sK0 sK2]
  have l58 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l49 sK1 sK0 sK2]
  have l59 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1]; rw [l58 sK0 X0 sK1 sK2]
  have l60 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l45 sK0]
    conv => enter [1]; rw [← l13 sK2 sK0 (sK0 ◇ sK0)]
  have l61 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l60 sK2 sK0]
    conv => enter [1]; rw [← l55 sK0 sK2 (sK0 ◇ sK0)]
  have l62 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l54 sK0 sK2]
    conv => enter [1]; rw [← l61 sK2 sK0]
  have l63 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK0]
    conv => enter [1]; rw [← l62 sK0 sK2]
  have l64 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l57 sK0 sK2]
    conv => enter [1]; rw [← l13 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l65 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK2 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l57 sK0 sK2]
  have l66 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2]; rw [l57 sK0 sK2]
    conv => enter [1]; rw [← l65 sK0 sK2 X0]
  have l67 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l64 sK2 sK0]
    conv => enter [1]; rw [← l55 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
  have l68 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l67 sK2 sK0]
  have l69 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l25 sK2 sK0]
  have l70 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l69 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l32 sK2 sK0]
  have l71 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [← l70 sK1 sK0 sK2]
  have l72 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h54075 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← l71 sK1 sK0 sK2]
  have l73 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l49 sK1 sK0 sK2]
    conv => enter [1]; rw [l72 sK1 sK0 sK2]
  have l74 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l73 sK1 sK0 sK2]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l73 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l76 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l73 sK1 sK0 sK2]
  have l77 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l73 sK1 sK0 sK2]
    conv => enter [1]; rw [← l76 sK1 sK0 sK2 X0]
  have l78 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l73 sK1 sK0 sK2]
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
  have l79 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l52 sK2 sK0]
  have l80 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK2 ◇ sK0)) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l52 sK2 sK0]
  have l81 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54075 (sK2 ◇ sK0) X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l80 sK0 sK2 X0]
  have l82 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l79 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l83 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l66 X0 sK0 sK2]
    conv => enter [1]; rw [← l81 sK2 sK0 X0]
  have l84 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l68 sK2 sK0]
    conv => enter [1]; rw [l82 sK0 sK2]
  have l85 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l84 sK2 sK0]
    conv => enter [1]; rw [← l14 sK2 sK0 (sK2 ◇ sK0)]
  have l86 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l84 sK2 sK0]
  have l87 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l86 sK1 sK0 sK2]
    conv => enter [1]; rw [← l36 sK1 sK0 sK2]
  have l88 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h54075 (sK2 ◇ sK0) (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [← l85 sK2 sK0]
  have l89 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l36 sK2 sK0 sK2]
    conv => enter [1]; rw [← l88 sK2 sK0]
  have l90 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l89 sK2 sK0]
    conv => enter [1, 2]; rw [← l63 sK0 sK2]
  have l91 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l90 sK2 sK0]
    conv => enter [1]; rw [← l52 sK2 sK0]
  have l92 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l91 sK2 sK0]
  have l93 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [l92 sK2 sK0]
  have l94 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l93 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l95 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l93 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK2 ◇ sK0) X0]
  have l96 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l63 sK0 sK2]
    conv => enter [1]; rw [l94 sK0 sK2]
  have l97 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l96 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
  have l98 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l68 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
  have l99 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [l98 sK1 sK2 sK0]
  have l100 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l87 sK1 sK0 sK2]
    conv => enter [1]; rw [l99 sK1 sK0 sK2]
  have l101 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l97 sK1 sK0 sK2]
    conv => enter [1]; rw [l100 sK1 sK0 sK2]
  have l102 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l73 sK1 sK0 sK2]
    conv => enter [1]; rw [← l18 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l103 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l18 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l14 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l104 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l103 sK2 sK0]
    conv => enter [1]; rw [← l95 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l105 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l102 sK1 sK0 sK2]
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
  have l106 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l104 sK2 sK0]
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK1]
  have l107 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l78 sK1 sK0 sK2]
    conv => enter [1]; rw [← l105 sK1 sK0 sK2]
  have l108 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l106 sK2 sK0 sK1]
  have l109 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l55 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l108 sK2 sK0 sK1]
  have l110 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l68 sK2 sK0]
    conv => enter [1]; rw [l109 sK0 sK2 sK1]
  have l111 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l93 sK0 sK2]
    conv => enter [1]; rw [l110 sK2 sK0 sK1]
  have l112 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2, 2]; rw [l107 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54075 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l113 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l112 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l77 X0 sK1 sK0 sK2]
  have l114 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l59 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l113 X0 sK1 sK0 sK2]
  have l115 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l111 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l116 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l115 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l114 sK1 sK0 sK1 sK2]
  have l117 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l116 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l87 sK1 sK0 sK2]
  have l118 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l117 sK2 sK0 sK1]
    conv => enter [1]; rw [← l83 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 sK2]
  have l119 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l101 sK1 sK0 sK2]
    conv => enter [1]; rw [← l118 sK2 sK0 sK1]
  have l120 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l119 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l121 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l93 sK0 sK2]
    conv => enter [1]; rw [← l120 sK1 sK0 sK2]
  have l122 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l111 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← l121 sK0 sK2 sK1]
  have l123 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l122 sK0 sK2 sK0]
    conv => enter [1]; rw [← l114 sK0 sK0 sK0 sK2]
  have l124 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l123 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l124 x z]
  conv => enter [1]; rw [l121 x z y]

theorem Equation4512_54075_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53846 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54075 X0 X2 X0]
    conv => enter [1, 2]; rw [h54075 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54075 (X0 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h54075 X2 (X0 ◇ X2) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54075 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ X0))]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X2 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← h54075 (X0 ◇ X0) X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [l3 X1 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X1 X1 X0]
    conv => enter [1]; rw [l4 X1 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l11 X0 X0 X1]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← h54075 X0 X1 X2]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l14 X0 X1 X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l16 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l13 y y x]
  conv => enter [1]; rw [← l17 y z x]

theorem Equation4512_54075_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53850 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 sK0]
  have l10 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ X0) X1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK0 X0]
  have l11 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0))) = (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h54075 ((sK2 ◇ sK0) ◇ X0) X1 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK2 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l14 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54075 (X1 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h54075 X0 X1 X1]
  have l15 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ sK0) X0 sK2]
    conv => enter [1, 2]; rw [← l9 sK2 sK0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54075 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X2 ◇ X3))]
  have l18 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54075 X0 X1 X2]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l18 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l22 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l14 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (X1 ◇ ((sK2 ◇ sK0) ◇ X0)))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [← l11 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) X0 (X1 ◇ ((sK2 ◇ sK0) ◇ X0))]
  have l25 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [← l10 sK0 X0 X1 sK2]
  have l26 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l21 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← l16 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l28 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0))) = (X1 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l24 X1 sK2 sK0 X0]
    conv => enter [1]; rw [← l22 X1 X0 (sK2 ◇ sK0)]
  have l29 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l25 X1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ X0))]
  have l30 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK2]
    conv => enter [1]; rw [h54075 sK0 X0 sK0]
  have l31 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l26 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l32 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK2]
    conv => enter [1]; rw [l27 sK0 X0]
  have l33 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l29 X1 sK2 sK0 X0]
    conv => enter [1]; rw [← l22 X1 X0 sK0]
  have l34 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l31 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l35 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l32 X0 sK2 sK0]
    conv => enter [1, 2]; rw [← l30 X0 sK2 sK0]
  have l36 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l33 X1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l20 sK0 X0]
  have l37 : ∀ sK0 X1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X1 X0 sK2
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK0 ◇ sK0)) X1 X0]
    conv => enter [1, 2, 2]; rw [← l30 X0 sK2 sK0]
  have l38 : ∀ sK0 X1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l37 sK0 X1 sK0 sK2]
    conv => enter [1]; rw [← h54075 (sK2 ◇ (sK2 ◇ sK0)) X1 sK0]
  have l39 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← l38 sK0 X1 sK2]
    conv => enter [1, 2]; rw [← l30 X1 sK2 sK0]
  have l40 : ∀ X1 sK2 sK0 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK2 sK0
    conv => enter [1]; rw [l35 X1 sK2 sK0]
    conv => enter [1]; rw [← l39 sK2 sK0 X1]
  have l41 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h54075 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 sK0]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ sK0) sK2]
  have l43 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK2]
  have l44 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54075 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h54075 sK0 sK0 sK2]
  have l45 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK2]
    conv => enter [1]; rw [l44 sK0 X0 sK2]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l43 sK0 sK2]
  have l47 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2 sK0]
    conv => enter [1]; rw [l42 sK0 sK2]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [l47 sK0 sK2]
  have l49 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
  have l50 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK0)) X0]
  have l51 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l30 sK2 sK2 sK0]
    conv => enter [1]; rw [l49 sK2 sK0]
  have l52 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK2]
    conv => enter [1]; rw [l51 sK2 sK0]
  have l53 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ (sK2 ◇ sK0))]
  have l54 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l53 sK0 sK2]
    conv => enter [1]; rw [← l30 sK0 sK2 sK0]
  have l55 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [← l54 sK0 sK2]
  have l56 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54075 (sK2 ◇ (sK2 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l55 sK0 sK2]
  have l57 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l56 sK2 sK0 X0]
    conv => enter [1]; rw [← l36 X0 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l58 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l57 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l30 (sK2 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l59 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l40 X0 sK2 sK0]
    conv => enter [1]; rw [l58 sK2 sK0 X0]
  have l60 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54075 (sK2 ◇ (sK2 ◇ sK0)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h54075 sK0 sK2 sK2]
  have l61 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h54075 sK0 sK2 sK2]
  have l62 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l61 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
  have l63 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l60 sK2 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l64 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l40 X0 sK2 sK0]
    conv => enter [1]; rw [l63 sK2 sK0 X0]
  have l65 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l52 sK0 sK2]
  have l66 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l65 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l67 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h54075 (sK0 ◇ sK0) (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l68 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [h54075 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l69 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = (((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l68 sK0 X0 X1]
  have l70 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l67 sK2 sK0]
    conv => enter [1, 2]; rw [← l30 sK2 sK2 sK0]
  have l71 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l69 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
  have l72 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l70 sK2 sK0]
    conv => enter [1]; rw [← h54075 (sK2 ◇ sK0) (sK0 ◇ sK0) sK2]
  have l73 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l71 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l74 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l72 sK2 sK0]
    conv => enter [1]; rw [l8 sK2 sK0 (sK2 ◇ sK0)]
  have l75 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) = (X0 ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← l73 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l36 sK0 sK2 sK0 X1]
  have l76 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l74 sK2 sK0]
    conv => enter [1]; rw [← l36 sK2 sK2 sK0 (sK2 ◇ sK0)]
  have l77 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l50 sK0 X1 X0]
    conv => enter [1]; rw [← l75 sK0 X0 X1 X0]
  have l78 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l76 sK2 sK0]
    conv => enter [1]; rw [l62 sK2 sK0 (sK2 ◇ sK0)]
  have l79 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [l36 X0 sK2 sK0 X1]
    conv => enter [1]; rw [l77 X0 sK0 X1]
  have l80 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l78 sK2 sK0]
    conv => enter [1]; rw [← l64 sK0 sK2 sK0]
  have l81 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [← l80 sK2 sK0]
  have l82 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l81 sK0 sK2]
    conv => enter [1]; rw [l7 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l83 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l82 sK0 sK2]
    conv => enter [1]; rw [← l12 sK0 sK2]
  have l84 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l83 sK0 sK2]
    conv => enter [1]; rw [h54075 sK0 sK2 sK2]
  have l85 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l84 sK0 sK2]
    conv => enter [1]; rw [← h54075 sK0 sK2 sK2]
  have l86 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK2 ◇ sK0)]
  have l87 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l88 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l89 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1, 2, 2]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [← h54075 (sK2 ◇ sK0) X0 sK0]
  have l90 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
  have l91 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l89 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l30 sK0 sK2 sK0]
  have l92 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l88 sK0 sK2]
    conv => enter [1]; rw [← l30 sK0 sK2 sK0]
  have l93 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l30 sK2 sK2 sK0]
    conv => enter [1]; rw [l87 sK2 sK0]
  have l94 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l86 sK0 sK2]
    conv => enter [1]; rw [← l30 (sK0 ◇ sK0) sK2 sK0]
  have l95 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l45 X0 sK2 sK0]
    conv => enter [1]; rw [← l91 sK2 sK0 X0]
  have l96 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [← l92 sK0 sK2]
  have l97 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK2]
    conv => enter [1]; rw [l93 sK2 sK0]
  have l98 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [← l94 sK0 sK2]
  have l99 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [l97 sK0 sK2]
  have l100 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l96 sK0 sK2]
    conv => enter [1]; rw [l8 sK2 sK0 (sK2 ◇ sK0)]
  have l101 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l100 sK2 sK0]
    conv => enter [1]; rw [← l36 sK2 sK2 sK0 (sK2 ◇ sK0)]
  have l102 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l101 sK2 sK0]
    conv => enter [1]; rw [l62 sK2 sK0 (sK2 ◇ sK0)]
  have l103 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l102 sK2 sK0]
    conv => enter [1]; rw [← l90 sK0 (sK2 ◇ sK0) sK2]
  have l104 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l98 sK0 sK2]
    conv => enter [1]; rw [← l103 sK2 sK0]
  have l105 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l104 sK0 sK2]
    conv => enter [1]; rw [← l30 (sK2 ◇ sK0) sK2 sK0]
  have l106 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l99 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l107 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l30 sK2 sK2 sK0]
    conv => enter [1]; rw [l106 sK2 sK0]
  have l108 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK2]
    conv => enter [1]; rw [l107 sK2 sK0]
  have l109 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [l108 sK0 sK2]
  have l110 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l105 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ (sK2 ◇ sK0))]
  have l111 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l30 sK2 sK2 sK0]
    conv => enter [1]; rw [l110 sK2 sK0]
  have l112 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK2]
    conv => enter [1]; rw [l111 sK2 sK0]
  have l113 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [l112 sK0 sK2]
  have l114 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l109 sK0 sK2]
  have l115 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [← l114 sK1 sK2 sK0]
  have l116 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l113 sK0 sK2]
  have l117 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [← l116 sK1 sK2 sK0]
  have l118 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h54075 (sK2 ◇ sK0) X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l115 sK1 sK2 sK0]
  have l119 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l115 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0) X0]
  have l120 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l95 X0 sK2 sK0]
    conv => enter [1]; rw [l118 sK2 sK0 X0 sK1]
  have l121 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l117 sK1 sK2 sK0]
    conv => enter [1]; rw [l40 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 sK0]
    conv => enter [1, 2]; rw [← l117 sK1 sK2 sK0]
  have l122 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l121 sK1 sK2 sK0]
  have l123 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l121 sK1 sK2 sK0]
    conv => enter [1]; rw [← l122 sK1 sK2 sK0 X0]
  have l124 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l41 sK2 sK0]
  have l125 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l124 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ (sK2 ◇ sK0))]
  have l126 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l125 sK2 sK0]
    conv => enter [1]; rw [l66 sK2 sK0]
  have l127 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l99 sK0 sK2]
    conv => enter [1]; rw [← l126 sK2 sK0]
  have l128 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l127 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ (sK0 ◇ sK0))]
  have l129 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l30 sK2 sK2 sK0]
    conv => enter [1]; rw [l128 sK2 sK0]
  have l130 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54075 sK0 sK2 sK2]
    conv => enter [1]; rw [l129 sK2 sK0]
  have l131 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l85 sK0 sK2]
    conv => enter [1]; rw [l130 sK0 sK2]
  have l132 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l131 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ (sK0 ◇ sK0))]
  have l133 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [l132 sK1 sK0 sK2]
  have l134 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h54075 (sK2 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [← l133 sK1 sK2 sK0]
  have l135 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l134 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l136 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l135 sK1 sK2 sK0 sK2]
    conv => enter [1]; rw [l17 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 sK2 (sK0 ◇ sK0)]
  have l137 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l136 sK2 sK0 sK1]
    conv => enter [1]; rw [← l22 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK0 ◇ sK0) sK2]
  have l138 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l137 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l15 sK0 sK2 sK2]
  have l139 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l138 sK2 sK0 sK1]
    conv => enter [1]; rw [l28 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 sK0 sK0]
  have l140 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l139 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [h54075 sK0 (sK2 ◇ sK0) sK2]
  have l141 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l119 sK1 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l140 sK2 sK0 sK1]
  have l142 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l117 sK1 sK2 sK0]
    conv => enter [1]; rw [l141 sK1 sK2 sK0]
  have l143 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) = (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [← h54075 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK2 X0]
    conv => enter [1, 2]; rw [← l142 sK1 sK2 sK0]
  have l144 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l143 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l145 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l120 (sK0 ◇ sK0) sK2 sK0 sK1]
    conv => enter [1]; rw [← l144 sK2 X0 sK0 sK1]
  have l146 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l145 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l34 (sK0 ◇ sK0) sK2 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l147 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l146 sK0 sK2 sK1]
    conv => enter [1]; rw [← l79 sK2 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l148 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l147 sK0 sK2 sK1]
    conv => enter [1]; rw [l62 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l149 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l148 sK0 sK2 sK1]
    conv => enter [1]; rw [← l90 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2]
  have l150 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [l149 sK0 sK2 sK1]
  have l151 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l150 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54075 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l152 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l151 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l123 X0 sK1 sK2 sK0]
  have l153 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l36 X0 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l152 X0 sK0 sK1 sK2]
  have l154 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1, 2]; rw [l30 (sK2 ◇ (sK2 ◇ sK0)) sK2 sK0]
    conv => enter [1]; rw [l153 X0 sK2 sK0 sK1]
  have l155 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l59 X0 sK2 sK0]
    conv => enter [1]; rw [l154 X0 sK2 sK0 sK1]
  have l156 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l155 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l157 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l150 sK0 sK1 sK2]
    conv => enter [1]; rw [← l156 sK1 sK2 sK0]
  have l158 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l157 sK0 sK1 sK2]
    conv => enter [1]; rw [← l45 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 sK0]
  have l159 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l117 sK1 sK2 sK0]
    conv => enter [1]; rw [← l158 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l159 y z x]

theorem Equation4512_54075_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53818 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54075 X0 X2 X0]
    conv => enter [1, 2]; rw [h54075 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54075 (X0 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h54075 X2 (X0 ◇ X2) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54075 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ X0))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X2 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← h54075 (X0 ◇ X0) X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← l3 X0 X1 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X1 X1]
    conv => enter [1]; rw [l4 X1 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l11 X0 X0 X1]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l12 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l13 x y z]

theorem Equation4512_54075_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53825 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
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
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l21 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK0 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h54075 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h54075 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [l21 sK0 X0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l20 sK0]
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l38 x y]

theorem Equation4512_54075_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
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
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l8 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h54075 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [l13 sK1 sK0 X0]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h54075 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← h54075 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ sK0) sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h54075 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l21 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l24 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l25 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l26 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK1]
  have l35 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l34 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l19 sK0 sK1]
  have l36 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l15 X0 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 X0 sK1]
  have l37 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1]; rw [← l36 X0 sK0 sK1]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l37 sK1 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 sK0 sK1 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1, 2]; rw [l44 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l45 x y]

theorem Equation4512_54075_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53812 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54075 X0 X2 X0]
    conv => enter [1, 2]; rw [h54075 X0 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ ((X0 ◇ X2) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54075 (X0 ◇ X2) X0 X1]
    conv => enter [1]; rw [← h54075 X2 (X0 ◇ X2) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54075 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ X0))]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X2 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [← h54075 (X0 ◇ X0) X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [l3 X1 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X1 X0]
    conv => enter [1]; rw [l3 X1 X1 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← l11 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 x y]
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation54075_implies_Equation53815 (G : Type*) [Magma G] (h54075 : Equation54075 G) : Equation53815 G := by
  intro x y
  conv => enter [1]; rw [h54075 x x y]

theorem Equation4512_54075_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation53835 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
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
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54075 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54075 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l6 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l9 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK1]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h54075 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1, 2]; rw [h54075 sK0 sK1 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) sK1 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l19 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK1]
    conv => enter [1]; rw [h54075 sK0 X0 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54075 sK0 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 sK0 sK1 sK1]
    conv => enter [1]; rw [h54075 sK0 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l26 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK0 ◇ sK0)) X0 sK1]
  have l27 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l9 X0 sK1 sK0]
    conv => enter [1]; rw [← l26 X0 sK1 sK0]
  have l28 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l27 X0 sK1 sK0]
  have l29 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l28 X0 sK1 sK0]
    conv => enter [1]; rw [l19 X0 sK1 sK0]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l29 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l23 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54075 (sK1 ◇ sK0) (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l15 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK0 sK1]
    conv => enter [1]; rw [← l33 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [← l23 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l30 (sK1 ◇ sK0) sK0 sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l38 x y]

end Semigroup5
