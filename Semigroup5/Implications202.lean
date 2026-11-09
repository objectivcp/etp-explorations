import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54031_implies_Equation54044 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54031 : Equation54031 G) : Equation54044 G := by
  have l0 : ∀ sK0 sK3 X0 : G, (sK0 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)) = (((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) ◇ X0) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [h4512 sK0 (sK3 ◇ (sK0 ◇ sK3)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK3 (sK0 ◇ sK3)]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0)) = ((sK0 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ X0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK3) (sK0 ◇ sK3) X0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54031 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ ((sK0 ◇ sK3) ◇ X0)) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK3 X0]
    conv => enter [1]; rw [← h54031 sK3 X0 sK0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h54031 sK1 X0 sK2]
  have l5 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54031 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ ((X0 ◇ X1) ◇ X2))]
  have l6 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h54031 sK1 X0 (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (sK1 ◇ X0)]
  have l7 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (X0 ◇ sK3)) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ X0)) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [h54031 sK3 X0 (sK0 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK3 ◇ X0)]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK1 sK2 X0]
  have l10 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ X0) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) X0]
    conv => enter [1]; rw [l3 sK3 sK0 X0]
  have l11 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3) := by
    intro sK3 X0 sK0
    conv => enter [1]; rw [← h54031 sK3 (sK0 ◇ sK3) X0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) sK3]
  have l12 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← h54031 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 sK2]
  have l13 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [← h54031 sK1 (sK3 ◇ (sK0 ◇ sK3)) X0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) sK1]
  have l14 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← h54031 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l15 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ sK0) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [← h54031 sK0 sK3 X0]
    conv => enter [1]; rw [h4512 sK0 sK3 sK0]
  have l16 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2 X0]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X2) X1 X0]
  have l17 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l17 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X1 X2]
    conv => enter [1]; rw [← l18 X0 X1 X2]
  have l20 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3) = (sK3 ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l11 sK3 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK3 (sK0 ◇ sK3)]
  have l21 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l11 sK3 (sK0 ◇ sK3) sK0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK3 ◇ (sK0 ◇ sK3))]
  have l22 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l20 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK0 ◇ sK3)]
  have l23 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l11 sK3 sK1 sK0]
    conv => enter [1]; rw [l22 sK3 sK0]
  have l24 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [h54031 (sK3 ◇ (sK0 ◇ sK3)) sK3 X0]
    conv => enter [1, 2, 2]; rw [← l11 sK3 sK1 sK0]
  have l25 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) = (sK3 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3)) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [← l24 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← l7 sK3 (sK3 ◇ (sK0 ◇ sK3)) sK0]
  have l26 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l10 sK3 sK0 (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [← l25 sK3 sK0 X0 sK1]
  have l27 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l21 sK3 sK0]
    conv => enter [1]; rw [l26 sK3 sK0 X0 sK1]
  have l28 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l11 sK3 sK1 sK0]
    conv => enter [1]; rw [l27 sK3 sK0 X0 sK1]
  have l29 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1, 2, 2]; rw [l21 sK3 sK0]
    conv => enter [1]; rw [← h54031 (sK3 ◇ (sK0 ◇ sK3)) (sK3 ◇ (sK0 ◇ sK3)) X0]
    conv => enter [1, 2]; rw [← l21 sK3 sK0]
  have l30 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1, 2, 2]; rw [l11 sK3 sK1 sK0]
    conv => enter [1]; rw [l29 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK3 sK1 sK0]
  have l31 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) = (sK3 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK3)) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l30 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← l7 sK3 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK0]
  have l32 : ∀ sK3 sK0 X0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 X0 sK1
    conv => enter [1]; rw [l31 sK3 sK0 X0 sK1]
    conv => enter [1]; rw [← l10 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l33 : ∀ sK3 sK1 sK0 : G, (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK1 sK0
    conv => enter [1]; rw [l28 sK3 sK1 sK0 sK3]
    conv => enter [1]; rw [l32 sK3 sK0 sK3 sK1]
  have l34 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) = ((sK0 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK1
    conv => enter [1, 2]; rw [l23 sK3 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK3 (sK0 ◇ sK3)]
  have l35 : ∀ sK0 sK3 sK1 : G, ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK0 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [← h4512 sK0 sK3 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [l34 sK0 sK3 sK1]
  have l36 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [l33 sK3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK3)) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l37 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l13 sK1 sK3 sK3 sK0]
    conv => enter [1]; rw [l36 sK1 sK3 sK0]
  have l38 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (X0 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 2, 2]; rw [l37 sK1 sK3 sK0]
    conv => enter [1]; rw [← h54031 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0]
    conv => enter [1, 2]; rw [← l37 sK1 sK3 sK0]
  have l39 : ∀ sK1 sK3 sK0 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1, 1]; rw [l37 sK1 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0]
  have l40 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK1 X0]
    conv => enter [1]; rw [l39 sK1 sK3 sK0 X0]
  have l41 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h54031 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK1 sK1]
    conv => enter [1]; rw [l38 sK1 sK3 sK0 sK1]
  have l42 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l6 sK1 X0 sK3 sK0]
    conv => enter [1]; rw [l40 sK1 sK3 sK0 X0]
  have l43 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) sK3 sK0]
    conv => enter [1]; rw [l41 sK1 sK3 sK0]
  have l44 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [l42 sK1 X0 sK3 sK0]
  have l45 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [l43 sK1 sK3 sK0]
  have l46 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l45 sK1 sK2 sK3 sK0]
  have l47 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l12 sK2 sK1 sK1]
  have l48 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l47 sK2 sK1]
  have l49 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l48 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l50 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l13 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK3 sK0]
    conv => enter [1, 2]; rw [← l46 sK1 sK2 sK3 sK0]
  have l51 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l13 sK1 (sK2 ◇ sK1) sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l52 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l51 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l46 sK1 sK2 sK3 sK0]
  have l53 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l50 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l52 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l53 sK1 sK1 sK1 sK2]
  have l55 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l14 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l56 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l55 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l57 : ∀ sK0 sK3 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ sK0) := by
    intro sK0 sK3
    conv => enter [1]; rw [← h4512 sK0 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [l15 sK0 sK3 sK3]
  have l58 : ∀ sK0 sK3 : G, ((sK0 ◇ sK3) ◇ sK0) = ((sK0 ◇ sK3) ◇ ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3))) := by
    intro sK0 sK3
    conv => enter [1]; rw [← l15 sK0 (sK3 ◇ (sK0 ◇ sK3)) sK3]
    conv => enter [1]; rw [l1 sK0 sK3 (sK0 ◇ sK3)]
  have l59 : ∀ sK0 sK3 sK1 : G, ((sK0 ◇ sK3) ◇ sK0) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [l58 sK0 sK3]
    conv => enter [1]; rw [← l35 sK0 sK3 sK1]
  have l60 : ∀ sK0 sK3 sK1 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [l57 sK0 sK3]
    conv => enter [1]; rw [l59 sK0 sK3 sK1]
  have l61 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l62 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l61 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l19 sK1 X0 X1]
  have l63 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1]; rw [← l62 sK1 sK2 X0 X1]
  have l64 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l9 sK1 sK2 sK2]
    conv => enter [1]; rw [l49 sK1 sK2]
  have l65 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l64 sK1 sK2]
    conv => enter [1]; rw [← l56 sK1 sK2]
  have l66 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l65 sK1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l67 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l54 sK1 sK2]
    conv => enter [1]; rw [← l66 sK1 sK2]
  have l68 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l66 sK1 sK2]
  have l69 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l68 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l70 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l65 sK1 sK2]
    conv => enter [1]; rw [l67 sK1 sK2]
  have l71 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l63 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l69 sK1 sK2 X0]
  have l72 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l54 sK1 sK2]
    conv => enter [1]; rw [l71 sK1 sK2 X0]
  have l73 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l65 sK1 sK2]
    conv => enter [1]; rw [l72 sK1 sK2 X0]
  have l74 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l70 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l75 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l73 sK1 sK2 X0]
    conv => enter [1]; rw [← l74 sK1 sK2 X0]
  have l76 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK3) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK3 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l75 sK1 sK2 (sK3 ◇ (sK0 ◇ sK3))]
  have l77 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l11 sK3 sK1 sK0]
    conv => enter [1]; rw [l76 sK3 sK0 sK1 sK2]
  have l78 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = (sK0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK3 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1, 2]; rw [l77 sK3 sK1 sK0 sK2]
  have l79 : ∀ sK3 sK1 sK0 X0 sK2 : G, (sK3 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK3)) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK3 sK1 sK0 X0 sK2
    conv => enter [1]; rw [h54031 sK3 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) X0]
    conv => enter [1, 2, 2]; rw [l77 sK3 sK1 sK0 sK2]
  have l80 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK3)) = (sK3 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK3)) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l79 sK3 sK1 sK0 sK3 sK2]
    conv => enter [1]; rw [← h54031 sK3 (sK1 ◇ (sK2 ◇ sK1)) sK3]
  have l81 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK3 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK3 (sK1 ◇ (sK2 ◇ sK1))]
  have l82 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) ◇ sK3)) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l80 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [← l10 sK3 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l83 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK3 sK0 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
    conv => enter [1]; rw [l82 sK3 sK1 sK0 sK2]
  have l84 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l33 sK3 sK1 sK0]
    conv => enter [1]; rw [l83 sK3 sK0 sK1 sK2]
  have l85 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l84 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [l77 sK3 sK1 sK0 sK2]
  have l86 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK3) ◇ (sK0 ◇ sK3)) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK3 sK1]
    conv => enter [1]; rw [l81 sK0 sK3 sK1 sK2]
  have l87 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = (sK3 ◇ ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [l86 sK0 sK3 sK1 sK2]
  have l88 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l87 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK1 ◇ (sK2 ◇ sK1))]
  have l89 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l88 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK3 sK0 sK1 sK2]
  have l90 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK3) ◇ sK0) = (sK0 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [← l15 sK0 (sK3 ◇ (sK0 ◇ sK3)) sK3]
    conv => enter [1, 2]; rw [l89 sK3 sK0 sK1 sK2]
  have l91 : ∀ sK0 sK3 sK1 sK2 : G, ((sK0 ◇ sK3) ◇ sK0) = ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK3 sK1 sK2
    conv => enter [1]; rw [l90 sK0 sK3 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK3 (sK1 ◇ (sK2 ◇ sK1))]
  have l92 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK0) = (sK3 ◇ ((sK0 ◇ sK3) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK3) sK0]
    conv => enter [1, 2]; rw [l91 sK0 sK3 sK1 sK2]
  have l93 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK0) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l92 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK3) (sK1 ◇ (sK2 ◇ sK1))]
  have l94 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK3)) ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l93 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK3 sK0 sK1 sK2]
  have l95 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l10 sK3 sK0 sK0]
    conv => enter [1]; rw [l94 sK3 sK0 sK1 sK2]
  have l96 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l95 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l14 sK1 sK3 sK2]
  have l97 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l65 sK1 sK2]
    conv => enter [1]; rw [← l96 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l97 x y z w]

theorem Equation4512_54044_implies_Equation54031 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54044 : Equation54044 G) : Equation54031 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54044 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54044 X0 X2 X0 X0]
  have l1 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h4512 X0 (X2 ◇ X0) X3]
    conv => enter [1, 1]; rw [l0 X0 X2 X1]
  have l2 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l1 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l3 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l2 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  intro x y z
  conv => enter [1]; rw [h54044 x y y x]
  conv => enter [1]; rw [l4 x y y z]

theorem Equation4512_54031_implies_Equation54012 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54031 : Equation54031 G) : Equation54012 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54031 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1]; rw [← h54031 sK0 X0 sK2]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54031 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ ((X0 ◇ X1) ◇ X2))]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54031 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ X0)]
  have l4 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))]
    conv => enter [1, 2]; rw [← h54031 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
  have l5 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 sK2 X0]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54031 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54031 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54031 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X2) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X2) X1 X0]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X1 X2]
    conv => enter [1]; rw [← l13 X0 X1 X2]
  have l15 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l19 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← l15 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54031 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 X0]
    conv => enter [1, 2, 2]; rw [l16 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l20 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l23 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← l7 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 sK0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l26 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l34 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54031 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l28 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l49 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l43 sK0 sK1]
  have l50 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l49 sK0 X0 sK1]
    conv => enter [1]; rw [l19 sK0 X0 sK0 sK1]
  have l51 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l50 sK0 X0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l52 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l51 sK0 X0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l53 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l53 x z y]

theorem Equation4512_54012_implies_Equation54031 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54012 : Equation54012 G) : Equation54031 G := by
  have l0 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h4512 X0 (X2 ◇ X0) X3]
    conv => enter [1, 1]; rw [h54012 X0 X2 X1]
  have l1 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l0 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X3]
  have l2 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l1 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l3 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X2 ◇ X0) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l2 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))) = (X0 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l3 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  intro x y z
  conv => enter [1]; rw [h54012 x y (x ◇ y)]
  conv => enter [1]; rw [l4 x x y z]

theorem Equation4512_54035_implies_Equation54045 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54035 : Equation54035 G) : Equation54045 G := by
  have l0 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ X0) ◇ (X1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ X0) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [← h54035 (sK1 ◇ X0) sK2 X1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54035 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l2 : ∀ sK1 X0 X1 sK2 : G, ((sK1 ◇ X0) ◇ (X1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [l0 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK2 ◇ sK1) ◇ X0)]
  have l3 : ∀ sK1 X0 sK2 X1 : G, (sK1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2 X1
    conv => enter [1]; rw [← l2 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK1 X0 (X1 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l3 sK1 X0 sK2 sK1]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h54035 (X0 ◇ X0) X0 (sK2 ◇ sK1)]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (X0 ◇ X0) X0]
  have l7 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [h54035 sK1 sK0 X0]
  intro x y z w
  conv => enter [1]; rw [l7 x y z w]

@[equational_result]
theorem Equation54045_implies_Equation54035 (G : Type*) [Magma G] (h54045 : Equation54045 G) : Equation54035 G := by
  intro x y z
  conv => enter [1]; rw [h54045 x y z y]

theorem Equation4512_54037_implies_Equation54043 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation54043 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) X0]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ X0) X1]
  have l3 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l4 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l3 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h54037 sK2 X0 sK1 X1]
  have l5 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l4 sK2 sK1 X0 X1]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK3 ◇ (sK0 ◇ sK2))]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [← l7 sK1 sK2 sK3 sK0]
  have l9 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK3 ◇ (sK0 ◇ sK2)) X0]
  have l10 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK1 ◇ (sK2 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0]
  have l11 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h54037 sK1 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK2 X0]
  have l12 : ∀ sK2 sK1 sK3 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK3 sK0 X0]
  have l13 : ∀ sK2 sK1 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l5 sK2 sK1 sK2 ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)]
    conv => enter [1]; rw [← l12 sK2 sK1 sK3 sK0 X0]
  have l14 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l13 sK2 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [← h54037 sK2 (sK3 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2)) sK2]
  have l15 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK3 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l5 sK2 sK1 sK3 ((sK0 ◇ sK2) ◇ X0)]
  have l16 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ sK2))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK2 sK1 X0 X1]
  have l17 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK2 sK1 X0 X1]
  have l18 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK1 X0 sK2 sK2]
  have l19 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l5 sK2 sK1 sK2 (X0 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK2 sK1 X0 X1]
  have l20 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ sK2)) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l5 sK2 sK2 (sK3 ◇ (sK0 ◇ sK2)) sK2]
    conv => enter [1]; rw [l15 sK2 sK2 sK3 sK0 sK2]
  have l21 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h4512 sK2 sK1 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l5 sK2 sK1 sK3 (sK0 ◇ sK2)]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l5 sK2 sK1 sK2 sK1]
  have l23 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [← l5 sK2 sK1 sK1 (sK3 ◇ (sK0 ◇ sK2))]
  have l24 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [← l5 sK2 sK1 sK1 (sK2 ◇ sK1)]
  have l25 : ∀ sK2 X0 : G, (sK2 ◇ (X0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54037 sK2 X0 (sK2 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l19 sK2 sK2 X0 sK2]
  have l26 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l14 sK2 sK3 sK2]
    conv => enter [1]; rw [l20 sK2 sK3 sK2]
  have l27 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [← l25 sK2 X0]
  have l28 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l21 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l26 sK2 sK3]
  have l29 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [← l28 sK2 sK1 sK3 sK0]
  have l30 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l23 sK2 sK1 sK3 sK0]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l30 sK1 sK2 sK3 sK0]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l24 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l33 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l32 sK1 sK2]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l29 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2]
    conv => enter [1]; rw [l34 sK1 sK2 sK3 sK0]
  have l36 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← l31 sK1 sK2 sK3 sK0]
  have l37 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l36 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
  have l38 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l18 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← l37 sK1 sK2 sK3 sK0 X0]
  have l39 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l38 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) sK1]
  have l40 : ∀ sK1 sK2 X0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l41 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l18 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l40 sK1 sK2 X0]
  have l42 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l41 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
  have l43 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l18 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [← l42 sK1 sK2 sK1]
  have l44 : ∀ sK1 sK2 X0 sK3 sK0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l35 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK3 ◇ (sK0 ◇ sK2)) X0]
  have l45 : ∀ sK1 sK2 X0 sK3 sK0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l44 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0 X0]
  have l46 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l39 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l45 sK1 sK2 X0 sK1 sK1]
  have l47 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l46 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l48 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l47 sK1 sK2 sK1]
    conv => enter [1]; rw [l18 sK1 sK2 (sK2 ◇ sK1) sK1]
  have l49 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l48 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l50 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l43 sK1 sK2]
    conv => enter [1, 2]; rw [← l49 sK1 sK2]
  have l51 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1, 2, 2]; rw [l49 sK1 sK2]
    conv => enter [1]; rw [← h54037 X0 (sK1 ◇ (sK2 ◇ sK1)) X1 sK1]
  have l52 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54037 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK1]
    conv => enter [1, 2]; rw [← l43 sK1 sK2]
  have l53 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l51 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l52 X0 sK1 sK2]
  have l54 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h54037 X0 X1 sK2 sK2]
    conv => enter [1, 2]; rw [← l27 sK2 sK1 X1]
  have l55 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l54 X0 X1 sK2 sK1]
    conv => enter [1]; rw [l53 X0 sK2 sK1 sK2]
  have l56 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l55 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h54037 X0 sK0 sK3 sK2]
  have l57 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l50 sK1 sK2]
    conv => enter [1]; rw [l56 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l57 x y z w]

theorem Equation4512_54043_implies_Equation54037 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54043 : Equation54043 G) : Equation54037 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ X0) X1]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l3 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (X1 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h54043 sK2 X1 sK1 X0]
  have l4 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (sK2 ◇ (X1 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l3 sK2 sK1 X0 X1]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK2 sK1 X0]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) = (sK2 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l5 sK2 sK1 X0]
    conv => enter [1]; rw [l4 sK2 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l7 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l6 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) X0 sK2]
  have l8 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l7 sK2 sK1 X0]
    conv => enter [1]; rw [← h54043 sK2 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l8 sK2 sK2 X0]
    conv => enter [1]; rw [← h54043 sK2 X0 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l10 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0)) = (sK1 ◇ (sK2 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l4 sK2 sK1 X1 X0]
  have l11 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h54043 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← l10 sK1 sK2 X1 X0]
  have l12 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l9 sK2 (sK3 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l4 sK2 sK1 sK1 (sK3 ◇ (sK2 ◇ sK0))]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 sK1 sK1]
  have l14 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l11 sK1 sK2 X0 X1]
  have l15 : ∀ sK1 sK2 X2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [l11 sK1 sK2 (sK1 ◇ sK1) X2]
    conv => enter [1]; rw [l14 sK1 sK2 sK1 sK1 X2]
  have l16 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l4 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l15 sK1 sK2 X0]
  have l17 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l12 sK2 sK1 sK3 sK0]
  have l18 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l17 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l0 sK2 sK1 (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
  have l19 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK2 sK1 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l18 sK2 sK1 sK2 sK2]
  have l20 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l19 sK2 sK1]
    conv => enter [1]; rw [← l9 sK2 (sK2 ◇ sK2)]
  have l21 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l20 sK2 sK1]
    conv => enter [1]; rw [l16 sK2 sK2 sK1]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK2]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l25 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l26 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 X0]
    conv => enter [1]; rw [← h54043 sK1 X0 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l27 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0]
    conv => enter [1]; rw [l26 sK1 sK2 X0]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l15 sK1 sK2 sK1]
  have l29 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54043 X0 X1 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l15 sK1 sK2 (X0 ◇ X1)]
  have l30 : ∀ X0 sK1 sK2 X1 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 X1 sK0
    conv => enter [1]; rw [← l29 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h54043 X0 sK0 X1 sK2]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [l30 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l31 x y z w]

theorem Equation4512_54037_implies_Equation54046 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation54046 G := by
  have l0 : ∀ sK3 sK2 X0 : G, ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ X0)) = (sK3 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 sK2 ((sK3 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ sK2) X0]
  have l1 : ∀ sK3 sK2 sK4 sK1 sK0 X0 : G, ((sK3 ◇ sK2) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK3 ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK3 sK2 sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK2 ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK3 sK2 X0 X1 : G, (((sK3 ◇ sK2) ◇ X0) ◇ X1) = (sK3 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 sK2 X0]
    conv => enter [1]; rw [← h4512 sK3 (sK2 ◇ X0) X1]
  have l3 : ∀ sK3 sK2 X0 X1 : G, (((sK3 ◇ sK2) ◇ X0) ◇ X1) = (sK3 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l2 sK3 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l4 : ∀ sK3 sK2 X0 X1 : G, (((sK3 ◇ sK2) ◇ X0) ◇ X1) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l3 sK3 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK3 X0 sK2 X1]
  have l5 : ∀ sK3 sK2 X0 X1 : G, ((sK3 ◇ sK2) ◇ (X0 ◇ X1)) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l4 sK3 sK2 X0 X1]
  have l6 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK3 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← l5 sK3 sK2 sK2 ((sK3 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ sK2) X0]
  have l7 : ∀ sK3 sK2 sK4 sK1 sK0 X0 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK3 ◇ sK2) ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK3 sK2 sK4 sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK3 sK2 sK2 ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l8 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK3 ◇ (X0 ◇ sK3))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK3 sK2 X0 X1]
  have l9 : ∀ sK3 sK2 X0 : G, ((sK3 ◇ sK2) ◇ sK3) = ((sK3 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 sK2 sK3]
    conv => enter [1]; rw [← l5 sK3 sK2 sK2 X0]
  have l10 : ∀ sK3 sK2 X0 : G, ((sK3 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ sK3)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l5 sK3 sK2 (sK2 ◇ (sK3 ◇ sK2)) X0]
    conv => enter [1]; rw [← l0 sK3 sK2 sK3]
  have l11 : ∀ sK3 sK2 sK4 sK1 sK0 X0 : G, ((sK3 ◇ sK2) ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK3 ◇ sK2) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK2 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l5 sK3 sK2 (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [← l1 sK3 sK2 sK4 sK1 sK0 sK3]
  have l12 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l8 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h54037 sK2 X0 sK3 sK3]
  have l13 : ∀ sK3 sK2 sK4 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK3 ◇ sK2) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l7 sK3 sK2 sK4 sK1 sK0 sK3]
    conv => enter [1]; rw [l11 sK3 sK2 sK4 sK1 sK0 sK3]
  have l14 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ sK3)) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l6 sK3 sK2 sK3]
    conv => enter [1]; rw [l10 sK3 sK2 sK3]
  have l15 : ∀ sK3 sK2 sK4 sK1 sK0 : G, ((sK3 ◇ sK2) ◇ sK3) = ((sK3 ◇ sK2) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK3)) := by
    intro sK3 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK3 sK2 sK3]
    conv => enter [1]; rw [l13 sK3 sK2 sK4 sK1 sK0]
  have l16 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ sK3) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [← h4512 sK3 sK2 sK3]
    conv => enter [1]; rw [l14 sK3 sK2]
  have l17 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK3) = (sK2 ◇ ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK2) sK3]
    conv => enter [1, 2]; rw [l9 sK3 sK2 (sK3 ◇ sK2)]
  have l18 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l17 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) (sK2 ◇ (sK3 ◇ sK2))]
  have l19 : ∀ sK3 sK2 sK4 sK1 sK0 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← l9 sK3 sK2 (sK3 ◇ sK2)]
    conv => enter [1]; rw [l9 sK3 sK2 (sK4 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK3) = (sK2 ◇ ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK2) sK3]
    conv => enter [1, 2]; rw [l9 sK3 sK2 (sK4 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK3) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l20 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l22 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l18 sK2 sK3]
    conv => enter [1]; rw [l21 sK2 sK3 sK4 sK1 sK0]
  have l23 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ X0)) = (((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK2)) sK3 X0]
    conv => enter [1, 1]; rw [l18 sK2 sK3]
  have l24 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l23 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK2)) (sK2 ◇ (sK3 ◇ sK2)) X0]
  have l25 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l24 sK2 sK3 X0]
    conv => enter [1]; rw [l12 sK2 sK3 (sK2 ◇ (sK3 ◇ sK2)) X0]
  have l26 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l12 sK2 sK3 sK3 sK2]
    conv => enter [1]; rw [l25 sK2 sK3 sK2]
  have l27 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, (((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1, 1]; rw [l22 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK2)) (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l28 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, (((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2)) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l27 sK2 sK3 X0 sK4 sK1 sK0]
    conv => enter [1]; rw [l12 sK2 sK3 (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  have l29 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2)) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK2)) (sK2 ◇ (sK3 ◇ sK2)) X0]
    conv => enter [1]; rw [l28 sK2 sK3 X0 sK4 sK1 sK0]
  have l30 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l12 sK2 sK3 (sK2 ◇ (sK3 ◇ sK2)) sK2]
    conv => enter [1]; rw [l29 sK2 sK3 sK2 sK4 sK1 sK0]
  have l31 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l26 sK2 sK3]
    conv => enter [1]; rw [l30 sK2 sK3 sK4 sK1 sK0]
  have l32 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2)) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l26 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK2 ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2)]
  have l33 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ sK3)) := by
    intro sK3 sK2
    conv => enter [1]; rw [l32 sK3 sK2]
    conv => enter [1]; rw [l10 sK3 sK2 sK2]
  have l34 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ sK3) := by
    intro sK3 sK2
    conv => enter [1]; rw [l33 sK3 sK2]
    conv => enter [1]; rw [← l16 sK3 sK2]
  have l35 : ∀ sK3 sK2 sK4 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [l34 sK3 sK2]
    conv => enter [1]; rw [l9 sK3 sK2 (sK4 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l35 sK3 sK2 sK3 sK3 sK3]
    conv => enter [1]; rw [← l19 sK3 sK2 sK3 sK3 sK3]
  have l37 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)) = ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [← h4512 sK3 sK2 (sK3 ◇ sK2)]
    conv => enter [1]; rw [l36 sK3 sK2]
  have l38 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) = (sK2 ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK2) (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2]; rw [← l37 sK3 sK2]
  have l39 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l38 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) (sK3 ◇ sK2)]
  have l40 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) = (((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ sK2)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK2)) (sK2 ◇ (sK3 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l39 sK2 sK3]
  have l41 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK3 ◇ sK2) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l40 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK2)) (sK3 ◇ sK2) X0]
  have l42 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK3 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l41 sK2 sK3 X0]
    conv => enter [1]; rw [l12 sK2 sK3 (sK3 ◇ sK2) X0]
  have l43 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l42 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) sK2]
  have l44 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [← l43 sK2 sK3 sK2]
    conv => enter [1]; rw [l12 sK2 sK3 (sK2 ◇ (sK3 ◇ sK2)) sK2]
  have l45 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2) := by
    intro sK2 sK3
    conv => enter [1]; rw [l26 sK2 sK3]
    conv => enter [1]; rw [← l44 sK2 sK3]
  have l46 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l26 sK2 sK3]
    conv => enter [1, 2]; rw [← l45 sK2 sK3]
  have l47 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l46 sK2 sK3]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK2)) X0]
  have l48 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ ((sK3 ◇ sK2) ◇ sK3)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK3)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1, 2]; rw [l15 sK3 sK2 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK3)]
  have l49 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ ((sK3 ◇ sK2) ◇ sK3)) = (sK2 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l48 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l12 sK2 sK3 (sK4 ◇ (sK1 ◇ sK0)) sK3]
  have l50 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ ((sK3 ◇ sK2) ◇ sK3)) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l49 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK4 ◇ (sK1 ◇ sK0)) sK2]
  have l51 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK3) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK2) sK3]
    conv => enter [1]; rw [l50 sK2 sK3 sK4 sK1 sK0]
  have l52 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l18 sK2 sK3]
    conv => enter [1]; rw [l51 sK2 sK3 sK4 sK1 sK0]
  have l53 : ∀ sK2 sK4 sK1 sK0 sK3 : G, ((sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ sK2) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK4 sK1 sK0 sK3
    conv => enter [1]; rw [← l52 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [l39 sK2 sK3]
  have l54 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l31 sK2 sK3 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [l53 sK2 sK2 sK2 sK2 sK3]
  have l55 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l54 sK2 sK3]
    conv => enter [1]; rw [← l47 sK2 sK3 (sK3 ◇ sK2)]
  have l56 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK3 ◇ sK2) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l55 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK2)) (sK3 ◇ sK2) X0]
  have l57 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK3 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l56 sK2 sK3 X0]
    conv => enter [1]; rw [l12 sK2 sK3 (sK3 ◇ sK2) X0]
  have l58 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ sK2) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l57 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) sK2]
  have l59 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l45 sK2 sK3]
    conv => enter [1]; rw [← l58 sK2 sK3 X0]
  have l60 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h54037 X0 X1 (sK2 ◇ (sK3 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l59 sK2 sK3 (X1 ◇ X0)]
  have l61 : ∀ X0 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← l60 X0 sK1 sK2 sK3]
    conv => enter [1]; rw [h54037 X0 sK1 sK4 sK0]
  have l62 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l46 sK2 sK3]
    conv => enter [1]; rw [l61 sK2 sK2 sK3 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l62 x y z w u]

@[equational_result]
theorem Equation54046_implies_Equation54037 (G : Type*) [Magma G] (h54046 : Equation54046 G) : Equation54037 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54046 sK1 sK2 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h54046 sK1 X0 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54046 X0 X1 sK1 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54046 sK1 sK2 X0 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK2]
  have l3 : ∀ X0 sK3 sK2 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h54046 X0 X0 sK3 sK2 sK0]
    conv => enter [1]; rw [l1 X0 X0 sK1 sK2]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK3 sK2 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation4512_54039_implies_Equation54041 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54039 : Equation54039 G) : Equation54041 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ X1 sK3 sK0 X0 sK1 : G, (X1 ◇ (((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro X1 sK3 sK0 X0 sK1
    conv => enter [1]; rw [h54039 X1 ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54039 X2 X0 X0]
    conv => enter [1, 2]; rw [h54039 X0 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54039 X2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h54039 X0 X1 X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← h54039 sK1 X0 (sK2 ◇ sK1)]
  have l6 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ sK1) ◇ (X1 ◇ (X1 ◇ X0))) = (sK2 ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54039 sK1 X0 X1]
  have l7 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h54039 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l8 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ X0))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54039 (sK2 ◇ sK1) X0 X1]
  have l9 : ∀ sK2 sK1 sK3 sK0 X1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0)))) = (sK2 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) := by
    intro sK2 sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [l1 sK2 sK1 sK3 sK0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54039 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0 X1]
  have l10 : ∀ sK2 sK1 sK3 sK0 X1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0)))) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) := by
    intro sK2 sK1 sK3 sK0 X1 X0
    conv => enter [1]; rw [l9 sK2 sK1 sK3 sK0 X1 X0]
    conv => enter [1]; rw [← l1 sK2 sK1 sK3 sK0 (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))))]
  have l11 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l8 sK1 sK2 X1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (X0 ◇ (sK2 ◇ sK1))]
  have l12 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ sK1) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK2 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l6 sK2 sK1 X1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ sK1)]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l14 : ∀ X1 sK1 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0))) = (X1 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X1 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l2 X1 sK3 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ (sK3 ◇ sK0)) X0 X1]
  have l15 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l10 sK2 sK1 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h54039 (sK3 ◇ (sK3 ◇ sK0)) X0 sK2]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54039 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1]
    conv => enter [1]; rw [l11 sK1 sK2 sK1 X0]
  have l17 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54039 (sK2 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [l12 sK2 sK1 sK2 X0]
  have l18 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l15 sK2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← l13 (sK2 ◇ sK1) (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l19 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l18 sK2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← l14 (sK2 ◇ sK1) sK1 sK3 sK0 X0]
  have l20 : ∀ X0 sK0 sK3 : G, (X0 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK0 sK3
    conv => enter [1]; rw [h54039 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h54039 sK0 sK0 sK3]
  have l21 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← h54039 X0 sK0 sK3]
    conv => enter [1]; rw [l20 X0 sK0 sK3]
  have l22 : ∀ X0 sK3 sK0 : G, (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [h54039 X0 (sK3 ◇ (sK3 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l21 sK0 sK3 sK0]
  have l23 : ∀ X0 sK3 sK0 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l21 X0 sK3 sK0]
    conv => enter [1]; rw [← l22 X0 sK3 sK0]
  have l24 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ X0)) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54039 X0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h54039 (sK2 ◇ sK1) (sK2 ◇ sK1) sK1]
  have l25 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) = (((sK2 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54039 ((sK2 ◇ sK1) ◇ X0) X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h54039 ((sK2 ◇ sK1) ◇ X0) (sK2 ◇ sK1) sK1]
  have l26 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = (((sK2 ◇ sK1) ◇ X0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h54039 ((sK2 ◇ sK1) ◇ X0) X0 X1]
    conv => enter [1, 2]; rw [h54039 X0 (sK2 ◇ sK1) sK1]
  have l27 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK1) ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (((sK2 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [← h54039 ((sK2 ◇ sK1) ◇ sK0) sK0 sK3]
    conv => enter [1, 2]; rw [h54039 sK0 (sK2 ◇ sK1) sK1]
  have l28 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [h54039 sK1 (sK2 ◇ sK1) sK1]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h54039 (sK2 ◇ sK1) (sK2 ◇ sK1) sK1]
  have l30 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = (sK2 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l1 sK2 sK1 sK3 sK0 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [h54039 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) (sK2 ◇ sK1) sK1]
  have l31 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l30 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l1 sK2 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l32 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l33 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l28 sK2 sK1]
  have l34 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK1) ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l27 sK2 sK1 sK0 sK3]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l35 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l26 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) X0 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l36 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l25 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l37 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← h54039 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l24 X0 sK2 sK1]
  have l38 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 sK2 sK1]
  have l39 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK1) ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l34 sK2 sK1 sK0 sK3]
    conv => enter [1]; rw [← h54039 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
  have l40 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l35 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h54039 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l41 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l36 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) X0 (X0 ◇ ((sK2 ◇ sK1) ◇ X0))]
  have l42 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK1) ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l39 sK2 sK1 sK0 sK3]
    conv => enter [1]; rw [l17 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l43 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l40 sK2 sK1 X0 X1]
    conv => enter [1]; rw [l17 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l44 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ (((sK2 ◇ sK1) ◇ X0) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l41 sK2 sK1 X0]
    conv => enter [1]; rw [← h54039 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ X0) X0]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l5 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l38 sK1 sK2]
  have l46 : ∀ sK2 sK1 sK0 sK3 : G, (((sK2 ◇ sK1) ◇ sK0) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [l42 sK2 sK1 sK0 sK3]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l47 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l43 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l48 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ (((sK2 ◇ sK1) ◇ X0) ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l44 sK2 sK1 X0]
    conv => enter [1]; rw [l17 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
  have l49 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l45 sK1 sK2]
  have l50 : ∀ sK2 sK1 sK0 sK3 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK2 sK1 sK0 sK3
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l46 sK2 sK1 sK0 sK3]
  have l51 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l47 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) X0 (X1 ◇ (X1 ◇ X0))]
  have l52 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l48 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) X0 sK1]
  have l53 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l21 (sK2 ◇ sK1) sK3 sK0]
    conv => enter [1]; rw [l50 sK2 sK1 sK0 sK3]
  have l54 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 (sK2 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [← l51 sK2 sK1 X0 sK2]
  have l55 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l53 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l54 sK2 sK1 X0]
  have l56 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l49 sK1 sK2]
  have l57 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l56 sK2 sK1]
  have l58 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l33 sK2 sK1]
    conv => enter [1]; rw [l57 sK2 sK1]
  have l59 : ∀ sK2 sK1 sK3 sK0 X0 X1 : G, ((sK2 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l55 sK2 sK1 sK3 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK1)]
  have l60 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l55 sK2 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [l59 sK2 sK1 sK2 sK2 X0 X1]
  have l61 : ∀ X0 sK3 sK0 sK2 sK1 : G, (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [h54039 X0 (sK3 ◇ (sK3 ◇ sK0)) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l55 sK2 sK1 sK3 sK0 sK1]
  have l62 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l55 sK2 sK1 sK3 sK0 sK1]
  have l63 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l62 sK2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l64 : ∀ X0 sK3 sK0 sK2 sK1 : G, (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l61 X0 sK3 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l58 sK2 sK1]
  have l65 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 X0 sK1 sK2]
    conv => enter [1]; rw [← l64 X0 sK3 sK0 sK2 sK1]
  have l66 : ∀ X0 sK3 sK0 sK1 sK2 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l23 X0 sK3 sK0]
    conv => enter [1]; rw [← l65 X0 sK1 sK2 sK3 sK0]
  have l67 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l31 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l63 sK2 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l68 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l67 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l52 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l69 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l7 sK2 sK1 sK1]
    conv => enter [1]; rw [← l68 sK2 sK1 sK3 sK0]
  have l70 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l69 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l19 sK2 sK1 sK3 sK0 (sK2 ◇ sK1)]
  have l71 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l70 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [← l60 sK2 sK1 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  have l72 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [l71 sK2 sK1]
  have l73 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1, 2, 2]; rw [← l72 sK2 sK1]
    conv => enter [1]; rw [← h54039 X0 sK2 (sK2 ◇ sK1)]
  have l74 : ∀ X0 sK2 sK1 : G, (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l58 sK2 sK1]
    conv => enter [1]; rw [l73 X0 sK2 sK1]
  have l75 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l37 X0 sK1 sK2]
    conv => enter [1]; rw [l74 X0 sK2 sK1]
  have l76 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK2 ◇ X0)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [l66 X0 sK3 sK0 X0 sK2]
    conv => enter [1]; rw [l75 X0 X0 sK2]
  intro x y z w
  conv => enter [1]; rw [← l76 x z w y]

@[equational_result]
theorem Equation54041_implies_Equation54039 (G : Type*) [Magma G] (h54041 : Equation54041 G) : Equation54039 G := by
  intro x y z
  conv => enter [1]; rw [h54041 x y z y]

theorem Equation4512_54048_implies_Equation54051 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54048 : Equation54048 G) : Equation54051 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54048 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54048 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54048 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X1]
  have l12 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))))) = (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [← l10 X1 X3 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
    conv => enter [1, 2, 2]; rw [← l10 X0 X1 X2]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h54048 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1, 2]; rw [l13 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [← l3 X0 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X1 X0]
    conv => enter [1, 2]; rw [← l10 X0 X1 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← h54048 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l3 X0 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l12 X1 X0 X0 X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2]; rw [h54048 X1 X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [l17 X1 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← l17 X0 X1]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1, 2]; rw [← l26 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 2, 2]; rw [← l26 X0 X1]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2, 2]; rw [← l26 X1 X0]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [l29 X0 X1]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X0]
    conv => enter [1]; rw [← l15 X1 X0]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l31 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1, 2]; rw [← l32 X1 X0]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l26 X1 X0]
  intro x y
  conv => enter [1]; rw [l34 x y]
  conv => enter [1]; rw [l33 y x]
  conv => enter [1]; rw [← l27 y x]

theorem Equation4512_54051_implies_Equation54048 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54051 : Equation54051 G) : Equation54048 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54051 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54051 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l5 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [l7 X1 X0 (X1 ◇ X2)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54051 X0 X1]
    conv => enter [1]; rw [l7 X1 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [h54051 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l9 X0 X1]
    conv => enter [1]; rw [l7 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l9 X0 X0]
    conv => enter [1]; rw [← l7 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← h54051 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X0]
    conv => enter [1, 2]; rw [← l9 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) (X0 ◇ (X1 ◇ X0))]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2, 2]; rw [← l7 X0 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l17 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ (X1 ◇ X0))]
  have l18 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← l8 X1 X0 (X1 ◇ (X0 ◇ X0))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0 X0]
    conv => enter [1]; rw [← l18 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0 X0]
    conv => enter [1]; rw [← l19 X0 X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 X1 X1]
    conv => enter [1]; rw [← l20 X1 X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ X0)]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X0)]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← l8 X0 X1 (X0 ◇ X0)]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← l26 X0 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1, 2]; rw [h54051 X1 X0]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h54051 X1 X0]
    conv => enter [1]; rw [l22 X0 X1]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l22 X0 X1]
    conv => enter [1]; rw [l7 X1 X0 (X0 ◇ X1)]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1]; rw [l30 X1 X0]
  have l32 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l29 X2 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1]; rw [l15 X1 X0]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l33 X0 X1]
    conv => enter [1]; rw [← l31 X0 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1]; rw [l26 X0 X1]
  have l36 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l34 X0 X1]
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1, 2]; rw [← l34 X0 X1]
  intro x y
  conv => enter [1]; rw [l36 x y]
  conv => enter [1, 2]; rw [l35 x y]
  conv => enter [1]; rw [← l32 y x x]

theorem Equation4512_54048_implies_Equation54058 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54048 : Equation54048 G) : Equation54058 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54048 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54048 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54048 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h54048 X0 X1]
    conv => enter [1]; rw [l10 X0 X1 (X0 ◇ X1)]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1, 2]; rw [← l12 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X1 X0]
    conv => enter [1, 2]; rw [← l10 X0 X1 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l3 X0 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2, 2]; rw [h54048 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [l15 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← l15 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2]; rw [← l20 X0 X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [← l22 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l20 X1 X0]
  intro x y
  conv => enter [1]; rw [l24 x y]
  conv => enter [1]; rw [l23 y x]

theorem Equation4512_54058_implies_Equation54048 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54058 : Equation54058 G) : Equation54048 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54058 X0 X1]
    conv => enter [1, 2]; rw [h54058 X1 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← h54058 X1 X0]
    conv => enter [1]; rw [h54058 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54058 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [h54058 X1 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X1]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [← l9 X1 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l10 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 X0 X1]
    conv => enter [1]; rw [l0 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X1]
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X2]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l17 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l20 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l22 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [← l21 X0 X1 ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l24 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← h54058 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h54058 (X1 ◇ X0) X0]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l12 X0 X0 ((X1 ◇ X0) ◇ X0)]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X0 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l27 X0 X1]
    conv => enter [1, 2, 2]; rw [l12 X0 X0 ((X1 ◇ X0) ◇ X0)]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 X0 X0]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1 X0]
    conv => enter [1]; rw [← l29 X0 X1]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54058 X0 X1]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [l31 x y]
  conv => enter [1]; rw [l30 x y]
  conv => enter [1]; rw [← l12 x x (y ◇ (x ◇ x))]
  conv => enter [1]; rw [← l8 y x x]

@[equational_result]
theorem Equation54087_implies_Equation54049 (G : Type*) [Magma G] (h54087 : Equation54087 G) : Equation54049 G := by
  intro x y z
  conv => enter [1]; rw [h54087 x y y z]

theorem Equation4512_54049_implies_Equation54087 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54049 : Equation54049 G) : Equation54087 G := by
  have l0 : ∀ sK1 X1 sK0 X0 : G, (sK1 ◇ (X1 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 X1 sK0 X0
    conv => enter [1]; rw [h54049 sK1 X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54049 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X1 sK0 X0 : G, (sK1 ◇ (X1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 X1 sK0 X0
    conv => enter [1]; rw [l0 sK1 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l3 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [← l2 sK1 X1 sK0 X0]
    conv => enter [1]; rw [h54049 sK1 X1 sK0]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54049 sK1 (sK2 ◇ sK1) sK1]
  have l5 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ X0) X1]
  have l6 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l5 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l8 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l6 sK1 sK2 X1 sK1]
  have l9 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54049 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK2]
  have l10 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l8 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK1 sK2 X0]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 sK2 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l10 X0 sK1 sK2]
  have l12 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54049 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l11 sK1 sK2 X0]
  have l13 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l12 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 X0]
  have l14 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l13 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l11 sK1 sK2 X1]
  have l15 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h54049 (sK1 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [l14 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK1 sK2]
  have l16 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← l3 X0 sK1 sK0 (sK1 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0 X0 X0]
  have l17 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l14 sK1 sK2 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l16 X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation4512_54087_implies_Equation54078 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54078 G := by
  have l0 : ∀ X2 sK3 sK0 X0 : G, (X2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X2 sK3 sK0 X0
    conv => enter [1]; rw [← h54087 sK3 X2 X2 sK0]
    conv => enter [1]; rw [h54087 sK3 X2 X0 sK0]
  have l1 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) sK3]
    conv => enter [1]; rw [h54087 sK3 (sK3 ◇ sK0) X0 sK0]
  have l2 : ∀ sK3 X0 sK0 : G, (sK3 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 X0 sK0
    conv => enter [1, 2]; rw [l0 X0 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK3 (sK3 ◇ sK0) (sK3 ◇ (sK3 ◇ sK0))]
  have l3 : ∀ X0 sK3 sK0 X1 X2 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK3 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK3 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ X0 sK3 sK0 X1 sK2 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK3 sK0 X1 sK2
    conv => enter [1]; rw [l3 X0 sK3 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK3 sK0 sK2]
  have l5 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) = (sK3 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l1 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l2 sK3 X0 sK0]
  have l6 : ∀ sK2 sK3 sK0 X1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X1 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X1
    conv => enter [1]; rw [l4 sK2 sK3 sK0 X1 sK2]
  have l7 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l5 sK3 sK0 sK3]
    conv => enter [1, 2]; rw [l0 sK3 sK3 sK0 sK2]
  have l8 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l6 sK2 sK3 sK0 sK3]
    conv => enter [1]; rw [← l7 sK3 sK0 sK2]
  have l9 : ∀ X1 sK3 sK0 X2 sK2 : G, (X1 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X2))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK3 sK0 X2 sK2
    conv => enter [1]; rw [← h54087 (sK3 ◇ (sK3 ◇ sK0)) X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK3 sK0 sK2]
  have l10 : ∀ X0 sK3 sK0 X1 sK2 : G, (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X1) := by
    intro X0 sK3 sK0 X1 sK2
    conv => enter [1]; rw [h4512 X0 (sK3 ◇ (sK3 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l0 X0 sK3 sK0 sK2]
  have l11 : ∀ sK2 sK3 sK0 X1 X2 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X1 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X2))) := by
    intro sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [l6 sK2 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l9 X1 sK3 sK0 X2 sK2]
  have l12 : ∀ sK2 sK3 sK0 X2 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X2)) := by
    intro sK2 sK3 sK0 X2
    conv => enter [1]; rw [l11 sK2 sK3 sK0 sK2 X2]
    conv => enter [1]; rw [l10 sK2 sK3 sK0 ((sK3 ◇ (sK3 ◇ sK0)) ◇ X2) sK2]
  have l13 : ∀ sK2 sK3 sK0 X2 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X2) := by
    intro sK2 sK3 sK0 X2
    conv => enter [1]; rw [l12 sK2 sK3 sK0 X2]
    conv => enter [1]; rw [l10 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) sK3 sK0 X2 sK2]
  have l14 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [l8 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK3 ◇ sK0)) sK3 X0]
  have l15 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l13 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l14 sK2 sK3 sK0 X0]
  have l16 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1)) = (((sK3 ◇ (sK3 ◇ sK0)) ◇ sK3) ◇ X1) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK3 ◇ (sK3 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l1 sK3 sK0 X0]
  have l17 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ X1)) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [l16 X0 sK3 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK3 ◇ sK0)) sK3 X1]
  have l18 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l15 sK2 sK3 sK0 X1]
    conv => enter [1]; rw [← l17 X0 sK3 sK0 X1]
  have l19 : ∀ sK2 sK3 sK0 X0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l18 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [h54087 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0 (sK2 ◇ sK1)]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h54087 sK1 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK2 sK3 sK0 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [l20 x y z w]

theorem Equation4512_54078_implies_Equation54087 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54078 : Equation54078 G) : Equation54087 G := by
  have l0 : ∀ X1 X2 sK1 sK0 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X1 X2 sK1 sK0 X0
    conv => enter [1]; rw [h54078 X1 X2 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ X1 X2 sK1 sK0 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X2 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X1 X2 sK1 sK0 X0
    conv => enter [1]; rw [l0 X1 X2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l2 : ∀ X2 sK1 sK0 X0 : G, (X2 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X2 sK1 sK0 X0
    conv => enter [1]; rw [← l1 X2 X2 sK1 sK0 X0]
    conv => enter [1]; rw [h54078 X2 X2 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54078 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [h54078 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l5 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l2 sK2 sK1 sK0 X0]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK0)]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 X0 sK1]
  have l8 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [h54078 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l8 x y z w]

theorem Equation4512_54087_implies_Equation54085 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54085 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h54087 sK0 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_54085_implies_Equation54087 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54085 : Equation54085 G) : Equation54087 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [h54085 sK1 sK0 X0]
  have l1 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h54085 (sK1 ◇ sK0) sK1 X1]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK3 sK1 sK0 X0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l2 sK1 sK0 X0 X1]
  have l4 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ sK1) = (X1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l1 sK1 sK0 X1 X0]
  have l5 : ∀ sK1 sK0 X1 sK3 : G, ((sK1 ◇ sK0) ◇ sK1) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X1 sK3
    conv => enter [1]; rw [l4 sK1 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← l3 sK3 sK1 sK0 (sK1 ◇ sK0) sK1]
  have l6 : ∀ sK3 sK1 sK0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X1
    conv => enter [1]; rw [← l0 sK1 sK0 sK3]
    conv => enter [1]; rw [l5 sK1 sK0 X1 sK3]
  have l7 : ∀ X1 X0 sK3 sK1 sK0 : G, (X1 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro X1 X0 sK3 sK1 sK0
    conv => enter [1, 2, 2]; rw [l6 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h54085 X0 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l8 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l6 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l9 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = (X1 ◇ (X0 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK3 sK1 sK0 X0 X0]
    conv => enter [1]; rw [← l7 X1 X0 sK3 sK1 sK0]
  have l10 : ∀ sK3 sK1 sK0 X0 X1 : G, ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l9 sK3 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l6 sK3 sK1 sK0 X0]
  have l11 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK3]
    conv => enter [1]; rw [← l10 sK3 sK1 sK0 X0 sK3]
  have l12 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [h54085 X0 X1 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l11 sK3 sK1 sK0 (X0 ◇ (X0 ◇ X1))]
  intro x y z w
  conv => enter [1]; rw [l12 x y z x w]

theorem Equation4512_54087_implies_Equation54108 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54108 G := by
  have l0 : ∀ X2 sK2 sK0 X0 : G, (X2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro X2 sK2 sK0 X0
    conv => enter [1]; rw [← h54087 sK2 X2 X2 sK0]
    conv => enter [1]; rw [h54087 sK2 X2 X0 sK0]
  have l1 : ∀ X0 sK2 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK2 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ (sK2 ◇ sK0))]
  have l2 : ∀ X0 sK2 sK0 X1 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 X1 sK3
    conv => enter [1]; rw [l1 X0 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK0 sK3]
  have l3 : ∀ sK3 sK2 sK0 X1 : G, (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK2 sK0 X1
    conv => enter [1]; rw [l2 sK3 sK2 sK0 X1 sK3]
  have l4 : ∀ X1 sK2 sK0 X2 sK3 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK2 sK0 X2 sK3
    conv => enter [1]; rw [← h54087 (sK2 ◇ (sK2 ◇ sK0)) X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 sK0 sK3]
  have l5 : ∀ X0 sK2 sK0 X1 sK3 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK2 sK0 X1 sK3
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ (sK2 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l0 X0 sK2 sK0 sK3]
  have l6 : ∀ sK3 sK2 sK0 X1 X2 : G, (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2))) := by
    intro sK3 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK3 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l4 X1 sK2 sK0 X2 sK3]
  have l7 : ∀ sK3 sK2 sK0 X2 : G, (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK3 sK2 sK0 X2
    conv => enter [1]; rw [l6 sK3 sK2 sK0 sK3 X2]
    conv => enter [1]; rw [l5 sK3 sK2 sK0 ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2) sK3]
  have l8 : ∀ sK3 sK2 sK0 X2 : G, (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X2) := by
    intro sK3 sK2 sK0 X2
    conv => enter [1]; rw [l7 sK3 sK2 sK0 X2]
    conv => enter [1]; rw [l5 (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 sK0 X2 sK3]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h54087 sK1 sK2 (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK3 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation4512_54108_implies_Equation54087 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54108 : Equation54108 G) : Equation54087 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54108 X0 sK1 X0 sK0]
    conv => enter [1]; rw [← h54108 sK0 sK1 X0 sK0]
  have l1 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [← h54108 sK0 sK1 sK3 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [← h54108 sK0 sK1 sK3 sK0]
    conv => enter [1]; rw [h54108 sK0 sK1 X0 sK0]
  have l3 : ∀ X0 sK1 sK0 X1 sK3 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) = ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 sK1 sK0 X1 sK3
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l2 X0 sK1 sK0 sK3]
  have l4 : ∀ sK1 sK0 X0 X1 sK2 : G, (((sK1 ◇ sK0) ◇ X0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1 sK2
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h54108 ((sK1 ◇ sK0) ◇ X0) sK1 X1 (sK2 ◇ sK1)]
  have l5 : ∀ X2 sK1 sK0 X0 sK2 : G, (X2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X2 sK1 sK0 X0 sK2
    conv => enter [1]; rw [← h54108 X2 sK1 X2 sK0]
    conv => enter [1]; rw [h54108 X2 sK1 X0 (sK2 ◇ sK1)]
  have l6 : ∀ sK3 sK1 sK0 X0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK3 sK1 sK0 X0 sK2
    conv => enter [1]; rw [l5 sK3 sK1 sK0 X0 sK2]
  have l7 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l4 sK1 sK0 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) X0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l8 : ∀ X1 sK1 sK2 sK0 sK3 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro X1 sK1 sK2 sK0 sK3 X0
    conv => enter [1]; rw [l7 X1 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [l3 X0 sK1 sK0 X0 sK3]
  have l9 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l6 sK3 sK1 sK0 sK3 sK3]
    conv => enter [1]; rw [l8 sK3 sK1 sK3 sK0 sK3 X0]
  have l10 : ∀ X0 sK1 X1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 X1 sK3 sK0
    conv => enter [1]; rw [h54108 X0 sK1 X1 (sK1 ◇ (X0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK3 sK1 sK0 sK1 X0]
  have l11 : ∀ sK3 sK1 sK0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X1
    conv => enter [1]; rw [l1 sK3 sK1 sK0 sK3]
    conv => enter [1]; rw [l10 sK3 sK1 X1 sK3 sK0]
  have l12 : ∀ sK3 sK1 sK0 X1 X0 : G, ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro sK3 sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [l11 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l13 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l9 sK3 sK1 sK0 ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK3)]
    conv => enter [1]; rw [← h54108 X0 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0) sK3]
  have l14 : ∀ sK3 sK1 sK0 X0 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK3 sK1 sK0 X0
    conv => enter [1]; rw [l13 sK3 sK1 sK0 X0]
    conv => enter [1]; rw [← l12 sK3 sK1 sK0 X0 X0]
  have l15 : ∀ sK3 sK1 sK0 X0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l14 sK3 sK1 sK0 (X1 ◇ (X1 ◇ sK3))]
    conv => enter [1]; rw [← h54108 X0 X1 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK3]
  intro x y z w
  conv => enter [1]; rw [← l15 z x w x y]

theorem Equation4512_54087_implies_Equation54151 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54151 G := by
  have l0 : ∀ X2 sK0 sK2 X0 : G, (X2 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X2 sK0 sK2 X0
    conv => enter [1]; rw [← h54087 sK0 X2 X2 sK2]
    conv => enter [1]; rw [h54087 sK0 X2 X0 sK2]
  have l1 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [l0 X0 sK0 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK0 ◇ sK2))]
  have l2 : ∀ X0 sK0 sK2 X1 sK3 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 X1 sK3
    conv => enter [1]; rw [l1 X0 sK0 sK2 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK0 sK2 sK3]
  have l3 : ∀ sK3 sK0 sK2 X1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X1
    conv => enter [1]; rw [l2 sK3 sK0 sK2 X1 sK3]
  have l4 : ∀ X1 sK0 sK2 X2 sK3 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X1 sK0 sK2 X2 sK3
    conv => enter [1]; rw [← h54087 (sK0 ◇ (sK0 ◇ sK2)) X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK0 sK2 sK3]
  have l5 : ∀ X0 sK0 sK2 X1 sK3 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ X1)) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) ◇ X1) := by
    intro X0 sK0 sK2 X1 sK3
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK0 ◇ sK2)) X1]
    conv => enter [1, 1]; rw [l0 X0 sK0 sK2 sK3]
  have l6 : ∀ sK3 sK0 sK2 X1 X2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ X2))) := by
    intro sK3 sK0 sK2 X1 X2
    conv => enter [1]; rw [l3 sK3 sK0 sK2 (sK0 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l4 X1 sK0 sK2 X2 sK3]
  have l7 : ∀ sK3 sK0 sK2 X2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ X2)) := by
    intro sK3 sK0 sK2 X2
    conv => enter [1]; rw [l6 sK3 sK0 sK2 sK3 X2]
    conv => enter [1]; rw [l5 sK3 sK0 sK2 ((sK0 ◇ (sK0 ◇ sK2)) ◇ X2) sK3]
  have l8 : ∀ sK3 sK0 sK2 X2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) ◇ X2) := by
    intro sK3 sK0 sK2 X2
    conv => enter [1]; rw [l7 sK3 sK0 sK2 X2]
    conv => enter [1]; rw [l5 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) sK0 sK2 X2 sK3]
  have l9 : ∀ sK3 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l8 sK3 sK0 sK2 (X0 ◇ (X0 ◇ sK3))]
    conv => enter [1]; rw [← h54087 X0 X1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) sK3]
  intro x y z w
  conv => enter [1]; rw [← l9 z w y x y]

theorem Equation4512_54151_implies_Equation54087 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54151 : Equation54151 G) : Equation54087 G := by
  have l0 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [← h54151 X1 sK0 X1 sK1]
    conv => enter [1]; rw [h54151 X1 sK0 X0 sK1]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [h54151 sK1 sK0 X0 sK1]
  have l2 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK1 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ X0 sK1 sK0 X1 sK3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 X1 sK3
    conv => enter [1]; rw [l2 X0 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK1 sK0 sK3]
  have l4 : ∀ sK3 sK1 sK0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 X1
    conv => enter [1]; rw [l3 sK3 sK1 sK0 X1 sK3]
  have l5 : ∀ X1 sK1 X2 sK0 X0 : G, (X1 ◇ (sK1 ◇ X1)) = (X2 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X1 sK1 X2 sK0 X0
    conv => enter [1]; rw [h54151 X1 sK1 X2 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK0 X0]
  have l6 : ∀ X1 sK1 X2 sK0 sK3 : G, (X1 ◇ (sK1 ◇ X1)) = (X2 ◇ ((sK1 ◇ sK0) ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X1 sK1 X2 sK0 sK3
    conv => enter [1]; rw [l5 X1 sK1 X2 sK0 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 sK1 sK0 sK3]
  have l7 : ∀ X2 sK3 sK1 sK0 X1 : G, (X2 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (sK1 ◇ X1)) := by
    intro X2 sK3 sK1 sK0 X1
    conv => enter [1, 2]; rw [l4 sK3 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l6 X1 sK1 X2 sK0 sK3]
  have l8 : ∀ sK3 sK1 sK0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK1 ◇ X1)) := by
    intro sK3 sK1 sK0 X1
    conv => enter [1]; rw [l4 sK3 sK1 sK0 sK3]
    conv => enter [1]; rw [l7 sK3 sK3 sK1 sK0 X1]
  have l9 : ∀ sK3 sK1 sK0 X0 X1 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK3 sK1 sK0 (sK1 ◇ X1)]
    conv => enter [1]; rw [← h54151 X0 X1 (sK1 ◇ X1) sK1]
  intro x y z w
  conv => enter [1]; rw [← l9 z x w x y]

theorem Equation4512_54087_implies_Equation54154 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54154 G := by
  have l0 : ∀ X2 sK1 sK0 X0 : G, (X2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X2 sK1 sK0 X0
    conv => enter [1]; rw [← h54087 sK1 X2 X2 sK0]
    conv => enter [1]; rw [h54087 sK1 X2 X0 sK0]
  have l1 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK1 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ X0 sK1 sK0 X1 sK4 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0 X1 sK4
    conv => enter [1]; rw [l1 X0 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK1 sK0 sK4]
  have l3 : ∀ sK4 sK1 sK0 X1 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 X1
    conv => enter [1]; rw [l2 sK4 sK1 sK0 X1 sK4]
  have l4 : ∀ X1 sK1 sK0 X2 sK4 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X1 sK1 sK0 X2 sK4
    conv => enter [1]; rw [← h54087 (sK1 ◇ (sK1 ◇ sK0)) X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK1 sK0 sK4]
  have l5 : ∀ X0 sK1 sK0 X1 sK4 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) = ((sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 sK1 sK0 X1 sK4
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l0 X0 sK1 sK0 sK4]
  have l6 : ∀ sK4 sK1 sK0 X1 X2 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2))) := by
    intro sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [l3 sK4 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l4 X1 sK1 sK0 X2 sK4]
  have l7 : ∀ sK4 sK1 sK0 X2 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2)) := by
    intro sK4 sK1 sK0 X2
    conv => enter [1]; rw [l6 sK4 sK1 sK0 sK4 X2]
    conv => enter [1]; rw [l5 sK4 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2) sK4]
  have l8 : ∀ sK4 sK1 sK0 X2 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X2) := by
    intro sK4 sK1 sK0 X2
    conv => enter [1]; rw [l7 sK4 sK1 sK0 X2]
    conv => enter [1]; rw [l5 (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 sK0 X2 sK4]
  have l9 : ∀ sK4 sK1 sK0 X0 X1 : G, (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l8 sK4 sK1 sK0 (X0 ◇ (X0 ◇ sK4))]
    conv => enter [1]; rw [← h54087 X0 X1 (sK4 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK4]
  intro x y z w u
  conv => enter [1]; rw [← l9 z w u x y]

@[equational_result]
theorem Equation54154_implies_Equation54087 (G : Type*) [Magma G] (h54154 : Equation54154 G) : Equation54087 G := by
  intro x y z w
  conv => enter [1]; rw [h54154 x y z x w]

theorem Equation4512_54053_implies_Equation54084 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54053 : Equation54053 G) : Equation54084 G := by
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
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54053 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54053 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54053 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54053 X0 X1 X2]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54053 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54053 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54053 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54053 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l17 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l9 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l22 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l17 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l24 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l22 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK0]
  have l26 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l24 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h54053 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54053 sK0 sK0 sK1]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54053 sK0 X0 sK1]
  have l32 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54053 sK0 X0 sK1]
  have l33 : ∀ sK0 X1 X0 sK1 : G, (sK0 ◇ (X1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [h54053 sK0 X1 X0]
    conv => enter [1, 2]; rw [h54053 sK0 X0 sK1]
  have l34 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X1 ◇ ((X0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h54053 (X0 ◇ sK0) X1 sK0]
    conv => enter [1, 2, 2]; rw [h54053 sK0 X0 sK1]
  have l35 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l34 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l36 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l33 sK0 X1 X0 sK1]
    conv => enter [1]; rw [l18 sK0 X1]
  have l37 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l32 sK0 X0 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [l31 sK1 sK0 X0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l41 : ∀ X0 sK0 X1 sK1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [l35 X0 sK0 X1 sK1]
    conv => enter [1]; rw [← l26 X0 X1 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0 sK0 sK0 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1 sK0]
    conv => enter [1]; rw [l36 sK1 sK0 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l45 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l41 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l36 X1 X0 sK0 X0]
  have l46 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (X1 ◇ (X0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l45 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 (X1 ◇ (X0 ◇ sK0))]
  have l47 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 X0 X1 X0]
    conv => enter [1]; rw [← l46 X0 X1 sK0]
  have l48 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l18 sK0 X0]
    conv => enter [1]; rw [l47 sK0 X0 X1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l51 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54053 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l39 sK0 sK1]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK1 X0]
    conv => enter [1]; rw [← l48 X0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l50 sK1 sK0]
  have l54 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l36 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l49 sK0 sK0]
  have l55 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l52 sK0 sK1 X0]
    conv => enter [1]; rw [l36 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK1]
  have l56 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l54 sK0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0]
    conv => enter [1]; rw [l55 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l63 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← l61 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l64 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l67 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1 X0]
  have l68 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l67 X0 sK0 sK1]
    conv => enter [1]; rw [l36 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK1]
  have l69 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l68 X0 sK0 sK1]
  have l70 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l69 sK0 X0 sK1]
  have l71 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l63 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l71 x y z]

@[equational_result]
theorem Equation54084_implies_Equation54053 (G : Type*) [Magma G] (h54084 : Equation54084 G) : Equation54053 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54084 X0 X1 X0]
    conv => enter [1]; rw [← h54084 X0 X2 X0]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h54084 sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK2 X1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l0 sK0 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_54053_implies_Equation54092 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54053 : Equation54053 G) : Equation54092 G := by
  have l0 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l2 sK2 sK0 X0]
  have l4 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l5 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK2]
  have l6 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l5 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l7 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54053 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54053 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l9 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h54053 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ sK0)]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK2 sK0 sK0]
  have l11 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 sK2 X0]
  have l12 : ∀ X0 sK0 X1 sK2 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X1 ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [h54053 (X0 ◇ sK0) X1 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK2 X0]
  have l13 : ∀ X0 sK0 X1 sK2 : G, ((X0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 X1 sK2
    conv => enter [1]; rw [l12 X0 sK0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l14 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (X1 ◇ (X0 ◇ sK0)))) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [← l13 X0 sK0 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 sK0 (X1 ◇ (X0 ◇ sK0))]
  have l15 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l7 sK0 X0 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0 sK0 sK2]
  have l16 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h54053 sK0 X0 sK2]
    conv => enter [1]; rw [l15 sK0 X0 X1 sK2]
  have l17 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ sK0)]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 1]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [l6 sK2 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK2]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l4 sK0 sK2]
    conv => enter [1]; rw [l19 sK0 sK2]
  have l21 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l20 sK0 sK2]
    conv => enter [1, 2]; rw [← l18 sK0 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h54053 sK0 (sK1 ◇ sK0) sK2]
  have l23 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h54053 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l24 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l23 sK2 sK0]
    conv => enter [1]; rw [l21 sK2 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54053 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK0)]
  have l26 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK2 ◇ sK0) X0]
  have l27 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l17 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l10 sK0 sK2]
  have l29 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 2]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 (X0 ◇ sK0)]
  have l30 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l27 sK0 sK2 (X0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l29 sK2 sK0 sK1 X0]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l11 sK0 sK2 sK0]
    conv => enter [1]; rw [l30 sK0 sK2 sK0 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
  have l33 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l22 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l33 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l35 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l34 sK0 sK2 sK0]
    conv => enter [1]; rw [← l27 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l36 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l35 sK0 sK2]
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0))]
  have l37 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [← l26 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l38 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l37 sK1 sK0 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54053 sK0 sK1 sK0]
    conv => enter [1]; rw [l38 sK1 sK0 sK0]
  have l40 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l41 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l40 sK2 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK2 sK1]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 sK2 sK0]
    conv => enter [1]; rw [l41 sK2 sK0 sK0]
  have l43 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54053 sK0 X0 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l24 sK0 sK2]
  have l44 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l43 sK0 X0 sK2]
    conv => enter [1]; rw [← l16 sK0 sK0 sK2 X0]
  have l45 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← l44 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l45 x y z]
  conv => enter [1]; rw [l18 x z]

theorem Equation4512_54092_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54092 : Equation54092 G) : Equation54053 G := by
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
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54092 X0 X1 X0]
    conv => enter [1]; rw [← h54092 X0 X2 X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54092 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54092 sK0 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l9 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l10 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X1 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [← l8 sK0 sK2 sK2]
    conv => enter [1]; rw [h54092 sK0 sK2 X1]
  have l11 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l10 sK2 sK0 X1]
    conv => enter [1, 2]; rw [l8 sK0 X1 sK2]
  have l12 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l9 sK0 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK0 X1]
    conv => enter [1, 2]; rw [l9 sK0 sK0 sK1]
  have l13 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK0 sK2 sK2]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK0 sK2 sK2]
  have l15 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l8 sK0 sK2 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK2 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK2 sK2]
  have l17 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h54092 (sK2 ◇ sK0) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 sK2]
  have l18 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l18 sK2 sK0 X0 sK1]
    conv => enter [1, 1]; rw [l16 sK0 sK2 sK1]
  have l20 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2, 1]; rw [l16 sK0 sK2 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 sK1]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 sK2 sK0 sK1]
  have l23 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 sK2 sK0 sK1]
  have l24 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l23 sK0 sK2 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2]
  have l26 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l24 sK2 sK0]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK0 sK2]
  have l28 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l26 sK2 sK0]
    conv => enter [1, 2]; rw [l16 sK0 sK2 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK2 ◇ sK0))]
  have l30 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l8 sK0 sK2 sK2]
    conv => enter [1]; rw [l28 sK2 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK0 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 sK0]
    conv => enter [1]; rw [l30 sK0 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l34 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l36 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK2 sK1]
    conv => enter [1]; rw [l35 sK1 sK0]
  have l37 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l34 sK2 sK0 sK1]
  have l38 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l6 (sK2 ◇ sK0) X0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 sK2]
  have l39 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0 sK1]
  have l41 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l37 sK2 sK0 sK1]
    conv => enter [1]; rw [← l38 sK2 sK0 X0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 sK0]
  have l43 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l41 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK2 sK0 sK2 sK1]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK2 (sK1 ◇ sK0)]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l43 sK2 sK0 sK1]
  have l46 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l45 sK0 sK1 sK2]
  have l47 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l36 sK1 sK0 sK2]
    conv => enter [1]; rw [← l46 sK1 sK0 sK2]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [← l47 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l48 x y z]

theorem Equation4512_54053_implies_Equation54096 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54053 : Equation54053 G) : Equation54096 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK1) X0]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54053 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54053 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ sK1)]
  have l5 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h54053 sK1 X0 sK2]
    conv => enter [1]; rw [h54053 sK1 X0 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ sK1)]
  have l7 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK0 ◇ sK1) X0]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l4 sK1 sK2 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h54053 (sK0 ◇ sK1) (sK2 ◇ sK1) sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK0 sK2]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l14 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h54053 sK1 (sK0 ◇ sK1) sK2]
  have l15 : ∀ sK1 X1 X0 sK2 : G, (sK1 ◇ (X1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 X1 X0 sK2
    conv => enter [1]; rw [h54053 sK1 X1 X0]
    conv => enter [1, 2]; rw [h54053 sK1 X0 sK2]
  have l16 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [← h54053 sK1 X1 sK2]
    conv => enter [1]; rw [l15 sK1 X1 X0 sK2]
  have l17 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l14 sK1 sK0 sK2]
    conv => enter [1]; rw [← l13 sK1 sK2 sK0]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54053 (sK1 ◇ (sK2 ◇ sK1)) X0 sK2]
    conv => enter [1, 2, 2]; rw [← h54053 sK1 sK2 sK2]
  have l19 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l16 X0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l18 sK1 sK2 X0]
  have l20 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK1 sK2]
    conv => enter [1]; rw [← l16 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 X0]
  have l21 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l17 sK1 sK0 sK2]
  have l22 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l21 sK1 sK0 sK2]
    conv => enter [1]; rw [← l16 (sK0 ◇ sK1) sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l23 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK0 sK2]
    conv => enter [1]; rw [l20 (sK0 ◇ sK1) sK1 sK2]
  have l24 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l23 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l25 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l24 sK2 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l23 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK2 sK1 sK0]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l26 sK1 sK0 sK2]
    conv => enter [1]; rw [l5 sK2 sK1 sK0 sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54053 sK1 sK2 sK2]
    conv => enter [1]; rw [← l27 sK1 sK0 sK2]
  have l29 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [l5 sK3 sK1 sK0 sK2]
    conv => enter [1]; rw [l20 sK3 sK1 sK2]
  have l30 : ∀ sK1 sK0 sK3 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [l23 sK1 sK0 sK1]
    conv => enter [1]; rw [← l29 sK3 sK1 sK0 sK1]
  have l31 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [l30 sK1 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l31 x y z w]

@[equational_result]
theorem Equation54096_implies_Equation54053 (G : Type*) [Magma G] (h54096 : Equation54096 G) : Equation54053 G := by
  intro x y z
  conv => enter [1]; rw [h54096 x y y z]

theorem Equation4512_54053_implies_Equation54109 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54053 : Equation54053 G) : Equation54109 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54053 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54053 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h54053 X0 (X1 ◇ X0) X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54053 X0 (X1 ◇ X0) X1]
    conv => enter [1]; rw [h54053 (X1 ◇ X0) X0 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54053 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l4 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54053 X0 X1 X2]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l4 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l6 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ (X1 ◇ X2))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l8 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X0]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0 X1]
    conv => enter [1, 2]; rw [← l0 X2 X1 X1 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1 X0]
    conv => enter [1, 2]; rw [← l0 X0 X1 X0 X1]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l8 X1 X0 X2]
  have l13 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l9 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l14 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 X0 X1]
    conv => enter [1]; rw [l10 X1 X2 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [← h54053 X0 X0 X1]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2 X1]
    conv => enter [1]; rw [l12 X1 X0 X2]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l13 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1, 2]; rw [l18 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1 X0]
    conv => enter [1]; rw [← l14 X0 X0 X0]
  have l21 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l20 X0 X2]
  have l23 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← l17 X0 (X0 ◇ X1) X1 X1]
  have l24 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l23 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l25 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X2]
    conv => enter [1]; rw [← l17 X0 X0 X1 X1]
  have l26 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l25 X0 X1 X2]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0 X1 X0]
    conv => enter [1]; rw [l26 X0 X1 X1]
  have l28 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l27 X1 X0]
  have l29 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l27 (X1 ◇ X2) X0]
  have l30 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l0 X2 X1 X0 X1]
    conv => enter [1]; rw [l29 X1 X2 X0]
  have l31 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l28 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l32 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l31 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l33 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l32 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l22 x x z]
  conv => enter [1]; rw [l30 x z y]
  conv => enter [1]; rw [l33 y z x]

theorem Equation4512_54109_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54109 : Equation54109 G) : Equation54053 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h54109 X0 sK1 sK0]
  have l4 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1]; rw [← h54109 X0 sK2 sK0]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ X0)]
    conv => enter [1]; rw [← h54109 X0 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [l4 sK0 sK2 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l8 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (X1 ◇ (sK2 ◇ (X1 ◇ X0))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l6 sK0 sK2 X0]
    conv => enter [1]; rw [h54109 X0 sK2 X1]
  have l9 : ∀ sK0 sK2 X0 X1 : G, (((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1, 1]; rw [l6 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ X0) X1]
  have l10 : ∀ sK0 sK2 X0 X1 : G, (((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l11 : ∀ sK0 sK2 X0 X1 : G, (((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l10 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← l8 sK0 sK2 X1 X0]
  have l12 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 sK2 X0 X1]
  have l13 : ∀ sK0 sK2 X0 sK1 : G, (((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [← l7 sK0 sK1 ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)]
  have l14 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (X1 ◇ (sK1 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [h54109 X0 sK1 X1]
  have l15 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ X0) X1]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 (sK2 ◇ sK0)]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = (X0 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l15 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l19 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ sK0)) X0 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [l13 sK0 sK2 X0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK1 sK0 sK2 (sK2 ◇ sK0)]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l14 sK0 sK1 X1 X0]
  have l22 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l12 sK0 sK2 X0 ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [l19 sK0 sK2 X0 sK1]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
  have l25 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l12 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [l22 sK0 sK2 sK1 X0]
  have l26 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l12 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l24 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [← l25 sK0 sK2 X0 sK1]
  have l28 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l26 sK0 sK2 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [l28 sK0 sK2 sK1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l6 sK0 sK2 sK0]
    conv => enter [1]; rw [l27 sK0 sK2 sK0 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK0]
    conv => enter [1]; rw [← l31 sK0 sK2 sK1]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 1]; rw [l32 sK0 sK2 sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h54109 (sK1 ◇ sK0) (sK1 ◇ sK0) sK0]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l32 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l12 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK0]
  have l40 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l39 sK0 sK2 sK1]
    conv => enter [1]; rw [l27 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l40 sK0 sK2 sK1]
  have l42 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l6 sK0 sK2 sK0]
    conv => enter [1]; rw [← l41 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [l42 sK0 sK2 sK1]
  have l44 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l45 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l44 sK1 sK0 sK2]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1 sK0]
    conv => enter [1]; rw [← l45 sK1 sK0 sK0]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1, 2]; rw [l32 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

end Semigroup5
