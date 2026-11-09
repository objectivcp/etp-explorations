import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54253_implies_Equation54178 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54253 : Equation54253 G) : Equation54178 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l2 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h54253 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 2, 2]; rw [← h54253 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54253 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l5 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54253 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X1))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54253 X0 X1 X0]
  have l8 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l5 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l9 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l10 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l2 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l11 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l8 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l12 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK1]
    conv => enter [1]; rw [h54253 sK2 sK1 X0]
  have l13 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ X2)) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l9 X3 X2 X0 X1]
    conv => enter [1]; rw [← l7 X1 X2 X0]
  have l14 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l10 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l15 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l11 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l16 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l14 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [l13 X0 X1 X0 X1]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l15 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l18 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l16 X2 X1 X0 X2]
    conv => enter [1]; rw [l13 X2 X1 X1 X1]
  have l19 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l18 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X1 X0]
    conv => enter [1]; rw [← l17 (X0 ◇ X1) X1 (X0 ◇ X1) X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l17 X1 X1 (X0 ◇ X1) X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X1 X1 X1 X0]
    conv => enter [1]; rw [← l22 X1 X0]
  have l24 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l12 sK2 sK1 X0]
    conv => enter [1]; rw [l12 sK2 sK1 X1]
  have l25 : ∀ X0 sK1 sK2 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1 X2
    conv => enter [1]; rw [l24 X0 sK1 sK2 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK2 ◇ sK1))]
  have l26 : ∀ X0 sK1 sK2 X1 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1 sK0
    conv => enter [1]; rw [l25 X0 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [l24 X0 sK1 sK2 sK0]
  have l27 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X1 sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l12 sK2 sK1 sK0]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l1 sK1 sK2 sK1]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 sK2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1 sK1]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54253 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK1)]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l34 x y z x]

theorem Equation4512_54253_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54253 : Equation54253 G) : Equation54261 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54253 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h54253 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 2, 2]; rw [← h54253 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54253 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l10 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54253 X0 X1 X2]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X1))]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54253 X0 X1 X0]
  have l13 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l10 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l15 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l8 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l16 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l7 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l17 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l13 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l4 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54253 sK0 sK1 X0]
  have l20 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ X2)) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l15 X3 X2 X0 X1]
    conv => enter [1]; rw [← l12 X1 X2 X0]
  have l21 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l16 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l22 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l17 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l23 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 X0]
  have l24 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l21 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [l20 X0 X1 X0 X1]
  have l25 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l22 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l26 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l23 sK1 X0]
  have l27 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l24 X2 X1 X0 X2]
    conv => enter [1]; rw [l20 X2 X1 X1 X1]
  have l28 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l27 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l28 X1 X1 X0]
    conv => enter [1]; rw [← l25 (X0 ◇ X1) X1 (X0 ◇ X1) X1]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l29 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l30 X1 X0]
    conv => enter [1]; rw [← l25 X1 X1 (X0 ◇ X1) X0]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l20 X1 X1 X1 X0]
    conv => enter [1]; rw [← l31 X1 X0]
  have l33 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
    conv => enter [1]; rw [l19 sK0 sK1 X1]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l19 sK0 sK1 X0]
  have l35 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l33 X0 sK1 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l35 X0 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [l33 X0 sK1 sK0 sK0]
  have l37 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l36 sK0 sK1 sK0 X1]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l38 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l39 sK1 sK0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h54253 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l44 sK1]
  have l46 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l32 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l46 z y x]

theorem Equation4512_54253_implies_Equation54215 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54253 : Equation54253 G) : Equation54215 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h54253 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 2, 2]; rw [← h54253 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54253 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54253 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h4512 X2 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54253 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X1))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← h54253 X0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54253 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54253 X0 (sK0 ◇ sK0) sK1]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54253 X0 X1 X0]
  have l13 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l7 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l9 sK0 sK1 (sK1 ◇ sK0)]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54253 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l18 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l3 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X0 ◇ (X1 ◇ X1))]
  have l19 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l13 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0 sK1]
    conv => enter [1]; rw [← l12 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h54253 sK1 sK0 X0]
  have l23 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X1 ◇ (X2 ◇ X2)) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l17 X3 X2 X0 X1]
    conv => enter [1]; rw [← l12 X1 X2 X0]
  have l24 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l18 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l25 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l19 X2 X1 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l21 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l28 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X3 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [l24 X2 X1 X0 X3]
    conv => enter [1, 2, 2]; rw [l23 X0 X1 X0 X1]
  have l29 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l25 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 X0]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0]
  have l32 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X1 ◇ X1)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l28 X2 X1 X0 X2]
    conv => enter [1]; rw [l23 X2 X1 X1 X1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2]; rw [← l22 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l32 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l36 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l34 X1 X1 X0]
    conv => enter [1]; rw [← l29 (X0 ◇ X1) X1 (X0 ◇ X1) X1]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l38 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1]; rw [← l29 X1 X1 (X0 ◇ X1) X0]
  have l40 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l23 X1 X1 X1 X0]
    conv => enter [1]; rw [← l39 X1 X0]
  have l41 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← l22 sK1 sK0 X0]
    conv => enter [1]; rw [l22 sK1 sK0 X1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l22 sK1 sK0 (sK0 ◇ sK0)]
  have l43 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l41 X0 sK0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK1 ◇ sK0))]
  have l44 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l43 X0 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l41 X0 sK0 sK1 sK0]
  have l45 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l44 sK0 sK0 sK1 X1]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54253 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h54253 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK0]
    conv => enter [1]; rw [← l48 sK1 sK0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1]; rw [← l51 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1 sK0]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l55 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l40 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l55 y z x]

theorem Equation4512_54253_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54253 : Equation54253 G) : Equation53828 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ X0))) = (X1 ◇ ((sK0 ◇ X0) ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h54253 sK2 (sK0 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54253 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54253 (sK2 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54253 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X1))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54253 X0 X1 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ X0))) = (X1 ◇ (sK0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ X0)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l5 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK2 ◇ sK0) ◇ X0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54253 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 sK0]
    conv => enter [1]; rw [h54253 sK2 sK0 X0]
  have l14 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ X0))) = (X1 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l11 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h54253 (sK2 ◇ sK0) X0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ X0))) = ((sK2 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l14 sK2 sK0 X0 sK2]
    conv => enter [1]; rw [← l9 (sK2 ◇ sK0) X0 sK2]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l18 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X0)) = (sK2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l16 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (sK0 ◇ X0)]
  have l19 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l18 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l20 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l19 sK2 sK0 X0]
    conv => enter [1]; rw [← h54253 sK0 X0 (sK2 ◇ sK0)]
  have l21 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l17 sK0]
    conv => enter [1]; rw [← l4 sK2 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l20 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l21 sK2 sK0]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l23 sK0 sK2]
  have l25 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 sK0]
    conv => enter [1]; rw [l24 sK0 sK2]
  have l26 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l25 sK0 sK2]
  have l27 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [l13 sK2 sK0 X0]
  have l28 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l13 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK0))]
  have l29 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← l13 sK2 sK0 sK1]
    conv => enter [1]; rw [l28 sK2 sK0 X0 X1]
  have l30 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l7 sK2 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 sK2 X0]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK0 sK2 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l30 sK2 sK0 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [← l31 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l32 x y z]

theorem Equation4512_53871_implies_Equation53880 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53871 : Equation53871 G) : Equation53880 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h53871 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
    conv => enter [1]; rw [← h53871 (X0 ◇ X1) X2 X3]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53871 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53871 X0 X1 (X1 ◇ X2)]
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1]; rw [← l0 X0 X1 X2 (X1 ◇ X0)]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ X0) X1]
  have l9 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l10 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l9 sK0 sK1 X1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53871 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h53871 sK0 X0 sK1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 X0 sK0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 X0 sK1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h53871 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation4512_53871_implies_Equation53881 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53871 : Equation53871 G) : Equation53881 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h53871 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
    conv => enter [1]; rw [← h53871 (X0 ◇ X1) X2 X3]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53871 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53871 X0 X1 (X1 ◇ X2)]
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1]; rw [← l0 X0 X1 X2 (X1 ◇ X0)]
  have l8 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ X0) X1]
  have l9 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l10 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l9 sK0 sK1 X1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53871 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h53871 sK0 X0 sK1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 X0 sK0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 X0 sK1]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h53871 sK0 sK2 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l17 sK0 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4512_53871_implies_Equation53879 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53871 : Equation53871 G) : Equation53879 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1]; rw [← h53871 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l5 : ∀ sK0 X1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ X1)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK0 X1 sK2 X0
    conv => enter [1]; rw [h53871 sK0 X1 ((sK2 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h53871 sK0 sK0 X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53871 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 X0 (sK2 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 X0 sK0]
  have l12 : ∀ sK0 X1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X0))) := by
    intro sK0 X1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l5 sK0 X1 sK2 X0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 sK0 sK1]
  have l18 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ X0) X1]
  have l19 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l20 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l13 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l19 sK0 sK1 X1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l26 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l10 sK0 X0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))]
  have l27 : ∀ sK0 X0 X1 sK2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) ◇ X1)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1, 1]; rw [l10 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) X1]
  have l28 : ∀ sK0 X0 X1 sK2 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X1))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l27 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) X1]
  have l29 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l14 sK0 X0]
    conv => enter [1]; rw [l26 sK0 X0 sK2]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 sK0 X1]
    conv => enter [1]; rw [← l28 sK0 X0 X1 sK0]
  have l31 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l29 sK0 X0 sK2]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l33 : ∀ sK0 sK1 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [l31 sK0 sK1 (X0 ◇ X1) sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  have l34 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0 sK0 sK0]
    conv => enter [1]; rw [← l32 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

theorem Equation4512_53871_implies_Equation53814 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53871 : Equation53871 G) : Equation53814 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ X1)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h53871 sK0 X1 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53871 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 X0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 X0 sK2]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l2 sK0 X1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l5 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l7 sK0 X0 X1]
    conv => enter [1]; rw [← l12 sK0 X0 X1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 sK0]
    conv => enter [1]; rw [← l16 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l19 x y z]

theorem Equation4512_54287_implies_Equation54194 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54194 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54287 X2 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h54287 X0 X1 X2 X2]
  have l1 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h54287 sK2 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK2 X0]
  have l2 : ∀ sK0 sK2 X0 X1 sK3 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0 X1 sK3
    conv => enter [1]; rw [h54287 (sK0 ◇ sK2) X0 X1 sK3]
    conv => enter [1, 2]; rw [h4512 sK3 (sK0 ◇ sK2) X0]
  have l3 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK2 sK2]
  have l4 : ∀ X1 sK3 sK0 sK2 X0 : G, (X1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l2 sK0 sK2 X0 X1 sK3]
    conv => enter [1]; rw [← l3 sK2 (sK0 ◇ sK2) X0]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54287 X0 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X0 X1 X3]
  have l6 : ∀ sK3 sK0 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [h54287 sK3 (sK0 ◇ sK2) X0 X1]
  have l7 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 sK2]
    conv => enter [1]; rw [h54287 sK0 sK2 X0 X1]
  have l8 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h54287 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l9 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l8 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l10 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l9 sK2 X0]
  have l11 : ∀ sK3 sK0 sK2 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l6 sK3 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  have l12 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK3 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) (X0 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l6 sK3 sK0 sK2 (sK0 ◇ sK2) X0]
  have l13 : ∀ sK0 sK2 sK3 X0 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [l7 sK0 sK2 sK3 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l12 sK3 sK0 sK2 X0]
  have l14 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l13 sK0 sK2 sK3 sK0]
    conv => enter [1]; rw [← l6 sK3 sK0 sK2 (sK3 ◇ (sK0 ◇ sK2)) sK0]
  have l15 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l14 sK0 sK2 sK3]
    conv => enter [1]; rw [l11 sK3 sK0 sK2]
  have l16 : ∀ X0 sK1 sK3 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l6 sK3 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [l11 sK3 sK0 sK2]
  have l17 : ∀ sK0 sK2 X0 X1 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 X0 X1 sK3
    conv => enter [1]; rw [h54287 (sK0 ◇ sK2) sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [l15 sK0 sK2 sK3]
  have l18 : ∀ sK0 sK2 X0 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = (((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0 sK3
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) sK2 X0]
    conv => enter [1, 1]; rw [l15 sK0 sK2 sK3]
  have l19 : ∀ sK0 sK2 X0 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0 sK3
    conv => enter [1]; rw [l18 sK0 sK2 X0 sK3]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK3 ◇ (sK0 ◇ sK2)) X0]
  have l20 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l17 sK0 sK2 sK0 sK0 sK3]
    conv => enter [1]; rw [← h54287 (sK2 ◇ sK2) (sK3 ◇ (sK0 ◇ sK2)) sK0 sK0]
  have l21 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [l4 (sK2 ◇ sK2) sK0 sK0 sK2 X0]
  have l22 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l20 sK0 sK2 sK3]
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ sK2) (sK3 ◇ (sK0 ◇ sK2))]
  have l23 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l22 sK0 sK2 sK3]
    conv => enter [1]; rw [← l10 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  have l24 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l23 sK0 sK2 sK3]
    conv => enter [1]; rw [← l6 sK3 sK0 sK2 sK2 (sK2 ◇ sK2)]
  have l25 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l24 sK0 sK2 sK3]
    conv => enter [1]; rw [l11 sK3 sK0 sK2]
  have l26 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← l25 sK0 sK2 sK3]
    conv => enter [1]; rw [l21 sK0 sK2 sK2]
  have l27 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK2 sK2 (sK2 ◇ sK2) sK0]
    conv => enter [1]; rw [← l26 sK2 sK3 sK0]
  have l28 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l27 sK2 sK3 sK0]
  have l29 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l28 sK2 sK3 sK0]
  have l30 : ∀ sK2 X0 sK1 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 sK1 sK3 sK0
    conv => enter [1]; rw [l29 sK2 sK3 sK0]
    conv => enter [1]; rw [← l16 X0 sK1 sK3 sK0 sK2]
  have l31 : ∀ X1 sK1 sK2 X0 sK3 sK0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← h54287 sK2 sK2 X1 sK1]
    conv => enter [1]; rw [l30 sK2 X0 sK1 sK3 sK0]
  have l32 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l31 X0 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l16 X0 sK1 sK3 sK0 sK2]
  have l33 : ∀ X1 sK3 sK0 sK2 X0 : G, (X1 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l7 sK0 sK2 X1 sK3]
    conv => enter [1]; rw [l7 sK0 sK2 X0 sK3]
  have l34 : ∀ sK1 sK3 sK0 sK2 X0 : G, (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l33 sK1 sK3 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l32 X0 sK1 sK2 sK3 sK0]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
    conv => enter [1]; rw [← l34 sK1 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l35 x y z w]

theorem Equation4512_54287_implies_Equation54244 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54244 G := by
  have l0 : ∀ sK1 sK0 sK2 X0 X1 X2 : G, (sK1 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ sK2) ◇ X0))) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [h54287 sK1 ((sK0 ◇ sK2) ◇ X0) X1 X2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK2) X0]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54287 X2 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h54287 X0 X1 X2 X2]
  have l2 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK1 (sK0 ◇ sK2)]
  have l3 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK2 sK2]
  have l4 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54287 X0 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X0 X1 X3]
  have l5 : ∀ X1 X2 sK1 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))) = ((sK0 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro X1 X2 sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l0 sK1 sK0 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h54287 (sK0 ◇ sK2) X0 sK1 ((sK0 ◇ sK2) ◇ X0)]
  have l6 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [h54287 sK1 (sK0 ◇ sK2) X0 X1]
  have l7 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 sK2]
    conv => enter [1]; rw [h54287 sK0 sK2 X0 X1]
  have l8 : ∀ X1 X2 sK1 sK0 sK2 X0 : G, (X1 ◇ (X2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X1 X2 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 X1 X2 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l3 sK2 (sK0 ◇ sK2) X0]
  have l9 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK2 sK2]
    conv => enter [1]; rw [l7 sK0 sK2 X0 X1]
  have l10 : ∀ X0 X1 sK1 sK0 sK2 X2 : G, (X0 ◇ ((X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X2)) = (((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) ◇ X2) := by
    intro X0 X1 sK1 sK0 sK2 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) X2]
    conv => enter [1, 1]; rw [← l6 sK1 sK0 sK2 X0 X1]
  have l11 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK2 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l12 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l6 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l11 sK1 sK0 sK2 sK1]
  have l13 : ∀ X0 X1 sK1 sK0 sK2 X2 : G, (X0 ◇ ((X1 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 X1 sK1 sK0 sK2 X2
    conv => enter [1]; rw [l10 X0 X1 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) X2]
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l9 sK0 sK2 sK1 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
  have l15 : ∀ X0 X1 sK1 sK0 sK2 X2 : G, (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X2))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro X0 X1 sK1 sK0 sK2 X2
    conv => enter [1, 2]; rw [h4512 X1 (sK1 ◇ (sK0 ◇ sK2)) X2]
    conv => enter [1]; rw [l13 X0 X1 sK1 sK0 sK2 X2]
  have l16 : ∀ sK2 sK0 X2 sK1 : G, ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X2)) := by
    intro sK2 sK0 X2 sK1
    conv => enter [1]; rw [← l8 sK2 sK2 sK1 sK0 sK2 X2]
    conv => enter [1]; rw [l15 sK2 sK2 sK1 sK0 sK2 X2]
  have l17 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l14 sK0 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK0 sK2 X0 sK0]
  have l18 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1, 2, 2]; rw [l14 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54287 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) X0 X1]
  have l19 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l14 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) X0]
  have l20 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [← l16 sK2 sK0 X0 sK0]
  have l21 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l18 X0 X1 sK0 sK2 X0]
    conv => enter [1]; rw [l2 X0 sK0 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l22 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l20 sK0 sK2 X0]
  have l23 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l21 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l3 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l24 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l23 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l22 sK0 sK2 (sK0 ◇ sK2)]
  have l25 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l24 X0 X1 sK0 sK2]
  have l26 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l25 sK0 sK2 sK0 sK0]
    conv => enter [1]; rw [← h54287 sK0 (sK2 ◇ sK2) sK0 sK0]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [← h54287 sK2 sK2 sK0 (sK2 ◇ sK2)]
  have l28 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [← l27 sK0 sK2]
    conv => enter [1]; rw [l17 sK0 sK2 X0 sK1]
  have l29 : ∀ X1 sK1 sK2 X0 sK0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X1 sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h54287 sK2 sK2 X1 sK1]
    conv => enter [1]; rw [l28 sK2 X0 sK0 sK1]
  have l30 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l17 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l29 X0 sK1 sK2 sK0 sK0]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 sK2 X0 sK1]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l32 x y z]

theorem Equation4512_54287_implies_Equation54253 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54253 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54287 sK0 sK1 X0 X1]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z y]

theorem Equation4512_54287_implies_Equation54219 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54219 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54287 sK0 sK1 X0 X1]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y y z]

theorem Equation4512_54287_implies_Equation53854 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation53854 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l8 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h54287 (sK1 ◇ sK1) sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h54287 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2, 2]; rw [l8 sK1]
  have l13 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK0 sK1]
  have l14 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 sK1 sK1]
  have l15 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1 sK1 sK1]
    conv => enter [1]; rw [← h54287 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 X0 X1]
  have l17 : ∀ sK3 sK0 sK1 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [h54287 sK3 (sK0 ◇ sK1) X0 X1]
  have l18 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [h54287 sK1 (sK1 ◇ sK1) X0 X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54287 sK0 sK1 X0 X1]
  have l20 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l16 sK1 X0 X1]
  have l22 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l8 sK1]
    conv => enter [1]; rw [l18 sK1 X0 X1]
  have l23 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1 sK1 sK1]
    conv => enter [1]; rw [← l22 sK1 sK1 sK1]
  have l25 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l23 sK1]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK1)]
  have l27 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h54287 sK1 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l26 sK1]
  have l28 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l27 sK1]
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l27 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l30 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [l28 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [l30 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l39 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54287 sK1 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l40 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54287 sK1 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l38 sK1 sK1]
  have l41 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l17 sK3 sK0 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l3 sK1 (sK3 ◇ (sK0 ◇ sK1))]
  have l42 : ∀ sK3 sK0 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK3 ◇ ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK1) (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l17 sK3 sK0 sK1 (sK0 ◇ sK1) X0]
  have l43 : ∀ sK0 sK1 sK3 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK3 X0
    conv => enter [1]; rw [l19 sK0 sK1 sK3 (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l42 sK3 sK0 sK1 X0]
  have l44 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l43 sK0 sK1 sK3 sK0]
    conv => enter [1]; rw [← l17 sK3 sK0 sK1 (sK3 ◇ (sK0 ◇ sK1)) sK0]
  have l45 : ∀ sK0 sK1 sK3 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [l44 sK0 sK1 sK3]
    conv => enter [1]; rw [l41 sK3 sK0 sK1]
  have l46 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l39 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l45 sK0 sK1 sK3]
  have l47 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l46 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [← l17 sK3 sK0 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l47 sK1 sK0 sK0]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1 sK1]
  have l50 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l50 x y z w]

theorem Equation4512_54287_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation54270 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [h54287 sK1 sK2 X0 X1]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l0 sK1 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z z]

theorem Equation4512_54287_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54287 : Equation54287 G) : Equation53818 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
  have l4 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h54287 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l6 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h54287 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54287 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← h54287 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0 sK0]
  have l9 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK0 sK0]
    conv => enter [1]; rw [h54287 sK2 sK0 X0 X1]
  have l10 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1]; rw [h54287 sK1 (sK2 ◇ sK0) X0 X1]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h54287 sK0 (sK1 ◇ (sK2 ◇ sK0)) X0 X1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK1 sK2 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l15 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK2 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l15 sK2 sK0 sK1]
  have l17 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
  have l18 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK2 ◇ sK0)]
  have l19 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l18 sK2 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 sK2 (sK2 ◇ sK0)]
  have l20 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l9 sK2 sK0 sK0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l19 sK0 sK2 sK2]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [← l20 sK2 sK0]
  have l22 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK2]
  have l24 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK2]
    conv => enter [1]; rw [l9 sK2 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l24 x x y z]

theorem Equation4512_53878_implies_Equation53892 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53892 G := by
  have l0 : ∀ sK3 sK0 sK2 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK3 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [← h4512 sK3 ((sK0 ◇ sK2) ◇ X0) X1]
  have l1 : ∀ sK3 sK0 sK2 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK3 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK3 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l2 : ∀ sK3 sK0 sK2 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h53878 sK3 (sK0 ◇ sK2) X0 X1]
  have l3 : ∀ sK3 sK0 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK0 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l2 sK3 sK0 sK2 X0 X1]
  have l4 : ∀ sK1 sK3 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l3 sK3 sK0 sK2 X0 X1]
  have l5 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK3 sK0 sK2 sK1 (sK1 ◇ sK2)]
  have l6 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l3 sK3 sK0 sK2 sK3 (sK0 ◇ sK2)]
  have l7 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l5 sK3 sK0 sK2 sK1]
  have l8 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK2)]
  have l9 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l6 sK3 sK0 sK2 sK1]
  have l10 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l9 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK2)]
  have l11 : ∀ sK1 sK3 sK0 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) ◇ X2) := by
    intro sK1 sK3 sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 sK1 sK3 sK0 sK2 X0 X1]
  have l12 : ∀ sK1 sK3 sK0 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((X0 ◇ X1) ◇ X2)) = (sK1 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X2)) := by
    intro sK1 sK3 sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l11 sK1 sK3 sK0 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2))) X2]
  have l13 : ∀ sK1 sK3 sK0 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((X0 ◇ X1) ◇ X2)) = (sK1 ◇ (sK3 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X2))) := by
    intro sK1 sK3 sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l12 sK1 sK3 sK0 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK3 (sK3 ◇ (sK0 ◇ sK2)) X2]
  have l14 : ∀ sK1 sK3 sK0 sK2 X0 X1 X2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((X0 ◇ X1) ◇ X2)) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l13 sK1 sK3 sK0 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h53878 sK1 sK3 (sK3 ◇ (sK0 ◇ sK2)) X2]
  have l15 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l4 sK1 sK3 sK0 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l14 sK1 sK3 sK0 sK2 sK1 sK1 sK1]
  have l16 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l3 sK3 sK0 sK2 sK3 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l15 sK1 sK3 sK0 sK2]
  have l17 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l16 sK1 sK3 sK0 sK2]
  have l18 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l10 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [l17 sK1 sK3 sK0 sK2]
  have l19 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK3) ◇ X0)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1, 1]; rw [l18 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK3) X0]
  have l20 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK3 ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK3 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK3 X0]
  have l21 : ∀ sK1 sK3 sK0 sK2 X0 : G, (((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [← h53878 sK1 sK1 sK3 X0]
  have l22 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l21 sK1 sK3 sK0 sK2 X0]
  have l23 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l4 sK1 sK3 sK0 sK2 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l22 sK1 sK3 sK0 sK2 sK1]
  have l24 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l3 sK3 sK0 sK2 sK3 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l23 sK1 sK3 sK0 sK2]
  have l25 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK3 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l24 sK1 sK3 sK0 sK2]
  have l26 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l10 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [l25 sK1 sK3 sK0 sK2]
  have l27 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53878 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ X1)]
  have l28 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l27 sK1 sK2 X0 X1]
  have l29 : ∀ sK1 sK2 X2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X2) := by
    intro sK1 sK2 X2
    conv => enter [1]; rw [l27 sK1 sK2 (sK1 ◇ sK1) X2]
    conv => enter [1]; rw [l28 sK1 sK2 sK1 sK1 X2]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53878 sK1 (sK1 ◇ sK2) sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK0 ◇ sK2)]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l30 sK1 sK2 sK1]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← h53878 sK1 sK1 sK1 sK2]
  have l33 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [← l26 sK1 sK3 sK0 sK2]
  have l34 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l4 sK1 sK3 sK0 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l32 sK1 sK2]
  have l35 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l34 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [l8 sK1 sK3 sK0 sK2]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l35 sK1 sK3 sK0 sK2]
  have l37 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l36 sK1 sK2 sK3 sK1]
    conv => enter [1]; rw [← h53878 sK1 sK3 sK3 (sK1 ◇ sK2)]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK3]
    conv => enter [1]; rw [h53878 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l38 x y z w]

theorem Equation4512_53878_implies_Equation53885 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53885 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53878 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53878 X0 (sK0 ◇ sK1) X0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0 X0]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK1) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X2) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l0 sK0 sK1 X0 X1]
  have l3 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X2) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 X2]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ X0 X1 X2 X3 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 X3 sK0 sK1
    conv => enter [1]; rw [← h53878 X0 X1 X2 X3]
    conv => enter [1]; rw [h53878 X0 X1 sK0 sK1]
  have l7 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h53878 X0 X0 X1 X2]
    conv => enter [1]; rw [h53878 X0 (X1 ◇ X2) sK0 sK1]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53878 X0 X0 sK0 sK1]
    conv => enter [1]; rw [l1 X0 sK0 sK1]
  have l9 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK0 ◇ sK1)]
  have l10 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l9 X0 X1 X0 sK0 sK1]
    conv => enter [1]; rw [l6 X0 X1 X0 (sK0 ◇ sK1) sK0 sK1]
  have l11 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l10 X0 X1 sK0 sK1]
    conv => enter [1]; rw [l8 X0 sK0 sK1]
  have l12 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53878 X0 X1 sK0 sK1]
    conv => enter [1]; rw [l11 X0 X1 sK0 sK1]
  have l13 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [← h53878 X0 sK2 sK1 sK2]
    conv => enter [1]; rw [l12 X0 sK2 sK0 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53878_implies_Equation53871 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53871 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53878 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53878_implies_Equation53875 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53875 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53878 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53878_implies_Equation53821 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53821 G := by
  have l0 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l1 sK1]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53878 sK1 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53878 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ X1)]
  have l6 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h53878 (sK1 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ X2))]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0 sK1 sK1]
    conv => enter [1]; rw [← h53878 (sK1 ◇ (sK1 ◇ sK1)) X0 sK1 sK1]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l5 sK1 X0 X1]
  have l9 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0 X1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l7 sK1 X0]
  have l11 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l8 sK1 X0 X1]
  have l12 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 X0 X1]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1 X0]
    conv => enter [1]; rw [l10 sK1 X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l13 sK1 X0]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l12 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l14 sK1 sK1]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53878 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1, 2]; rw [← l12 sK1 X0 X0]
  have l17 : ∀ X0 X1 X2 X3 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 X3 sK1
    conv => enter [1]; rw [← h53878 X0 X1 X2 X3]
    conv => enter [1]; rw [h53878 X0 X1 sK1 sK1]
  have l18 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X2) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h53878 X0 X0 X1 X2]
    conv => enter [1]; rw [h53878 X0 (X1 ◇ X2) sK1 sK1]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53878 X0 X0 sK1 sK1]
    conv => enter [1]; rw [l16 X0 sK1]
  have l20 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [l18 X0 X1 X2 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK1 ◇ sK1)]
  have l21 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l20 X0 X1 X0 sK1]
    conv => enter [1]; rw [l17 X0 X1 X0 (sK1 ◇ sK1) sK1]
  have l22 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← l21 X0 X1 sK1]
    conv => enter [1]; rw [l19 X0 sK1]
  have l23 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h53878 X0 X1 sK1 sK1]
    conv => enter [1]; rw [l22 X0 X1 sK1]
  have l24 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h53878 X0 sK2 sK3 sK0]
    conv => enter [1]; rw [l23 X0 sK2 sK1]
  have l25 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l15 sK1]
  intro x y z w
  conv => enter [1]; rw [← l25 x y z w]

theorem Equation4512_53878_implies_Equation53877 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53877 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53878 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53878_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53878 : Equation53878 G) : Equation53818 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l1 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53878 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53878 sK0 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ X1)]
  have l6 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h53878 (sK0 ◇ sK0) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (X1 ◇ X2))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h53878 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l7 sK0 X0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53878 X0 (sK0 ◇ sK0) X0 X0]
    conv => enter [1, 2]; rw [← l12 sK0 X0 X0]
  have l17 : ∀ X0 X1 X2 X3 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 X3 sK0
    conv => enter [1]; rw [← h53878 X0 X1 X2 X3]
    conv => enter [1]; rw [h53878 X0 X1 sK0 sK0]
  have l18 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h53878 X0 X0 X1 X2]
    conv => enter [1]; rw [h53878 X0 (X1 ◇ X2) sK0 sK0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53878 X0 X0 sK0 sK0]
    conv => enter [1]; rw [l16 X0 sK0]
  have l20 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l18 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 X0 sK0]
    conv => enter [1]; rw [l17 X0 X1 X0 (sK0 ◇ sK0) sK0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l21 X0 X1 sK0]
    conv => enter [1]; rw [l19 X0 sK0]
  have l23 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h53878 (X0 ◇ X1) X2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l24 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l23 X0 X1 X2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l25 : ∀ X0 X1 X2 sK0 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l24 X0 X1 X2 sK0 X0 X0]
    conv => enter [1]; rw [l17 X0 X1 X2 (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) sK0]
  have l26 : ∀ X0 X1 X2 sK0 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l25 X0 X1 X2 sK0]
    conv => enter [1]; rw [l22 X0 X1 sK0]
  have l27 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l26 X0 X1 X2 sK0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53878 X0 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l27 X0 X1 X0 sK0]
  have l29 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h53878 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l28 X0 sK1 sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

theorem Equation4512_54241_implies_Equation54185 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54185 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l7 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (((sK1 ◇ sK1) ◇ X0) ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [h54241 X1 (sK1 ◇ sK0) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK0 X0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l5 sK1 sK0]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54241 X1 X2 X0]
    conv => enter [1]; rw [h54241 X1 X2 X2]
    conv => enter [1, 2]; rw [h54241 X1 X2 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54241 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54241 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l14 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54241 sK2 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK0) X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54241 (sK1 ◇ sK0) sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l17 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ (X1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54241 X0 X1 sK0]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54241 sK1 X0 sK1]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54241 sK0 X0 sK1]
  have l20 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54241 X0 X1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ sK1))]
  have l21 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l16 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l14 sK2 sK1 sK0 X0]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l27 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l28 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l8 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)))]
  have l29 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l31 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l24 sK1 X0]
  have l32 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l21 X2 X0 X1 X1]
    conv => enter [1]; rw [← l27 X2 X0 X1]
  have l33 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l28 X0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l26 sK0 sK1 sK1]
  have l34 : ∀ X1 sK1 sK0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l29 X1 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← l21 X1 sK1 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK1 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l36 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l33 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h54241 X0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l37 : ∀ X1 sK1 sK0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l34 X1 sK1 sK0]
    conv => enter [1, 2]; rw [l32 X1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l38 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l39 : ∀ X1 sK1 sK0 : G, (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l37 X1 sK1 sK0]
    conv => enter [1]; rw [← l20 sK1 X1 sK1]
  have l40 : ∀ X1 sK1 sK0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [h54241 X1 sK1 sK1]
    conv => enter [1]; rw [← l39 X1 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [h54241 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l36 (sK1 ◇ sK1) sK1 sK0]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l48 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [h54241 X0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l43 sK0 sK1]
  have l49 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK1]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l51 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l44 sK0 sK1]
  have l52 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l51 X0 sK1 sK0]
    conv => enter [1]; rw [← l48 X0 sK0 sK1]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [← l50 sK1 sK0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l53 sK1 sK0]
  have l55 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l54 sK0 sK1]
  have l56 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l55 X0 sK1 X0]
    conv => enter [1, 2]; rw [← l52 X0 sK1 X0]
  have l57 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h54241 X0 sK1 sK1]
  have l58 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h54241 X1 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h54241 X0 sK1 sK1]
  have l59 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l58 X1 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l60 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l56 X0 sK1]
    conv => enter [1]; rw [← l57 sK1 X0]
  have l61 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l59 X1 sK1 X0]
    conv => enter [1]; rw [← l9 (sK1 ◇ sK1) X1 X0]
  have l62 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l49 sK2 sK1 sK0]
    conv => enter [1]; rw [← l52 sK2 sK1 sK0]
  have l63 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l62 sK2 sK1 sK0]
  have l64 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l61 X0 sK1 (sK2 ◇ (sK1 ◇ X0))]
    conv => enter [1]; rw [← l63 X0 sK2 sK1 X0]
  have l65 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h54241 sK2 sK1 sK0]
    conv => enter [1]; rw [← l62 sK2 sK1 sK0]
  have l66 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [h54241 sK2 sK1 sK0]
  have l67 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l64 X0 sK1 sK2]
    conv => enter [1]; rw [l66 X0 sK2 sK1 sK0]
  have l68 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l65 sK0 sK2 sK1]
  have l69 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l67 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l68 X0 sK2 sK1 sK0]
  have l70 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l23 sK2 sK1 sK0 X0]
  have l71 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l23 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK2 ◇ (sK1 ◇ sK0)) ◇ sK1)]
  have l72 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l71 sK1 sK2 sK0]
    conv => enter [1]; rw [l18 sK1 (sK2 ◇ (sK1 ◇ sK0))]
  have l73 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l69 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l70 X0 sK2 sK1 sK0]
  have l74 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l60 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l72 sK1 sK2 sK0]
  have l75 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l73 sK1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l74 sK2 sK1 sK0]
  have l76 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l65 sK0 sK2 sK1]
    conv => enter [1]; rw [← l75 sK1 sK2 sK0]
  have l77 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l76 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l77 x y z]

theorem Equation4512_54241_implies_Equation54219 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54219 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l11 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l12 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l13 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l10 sK2 sK0 sK1]
  have l14 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l15 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (((sK2 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54241 X1 (sK1 ◇ sK1) ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK2 sK0 X0]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54241 X0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK1]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54241 X1 X2 X0]
    conv => enter [1]; rw [h54241 X1 X2 X2]
    conv => enter [1, 2]; rw [h54241 X1 X2 X0]
  have l18 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54241 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54241 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l22 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54241 sK1 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l23 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54241 sK2 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) X0]
  have l24 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h54241 sK2 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [l14 sK2 sK0 sK1 X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54241 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l26 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l27 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54241 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l28 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l29 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l26 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l31 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h54241 (sK2 ◇ (sK0 ◇ sK1)) sK1 sK2]
    conv => enter [1]; rw [← l24 sK2 sK0 sK1 sK2]
  have l32 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l23 sK2 sK0 sK1 X0]
  have l33 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l22 sK1 sK2 sK0 X0]
  have l34 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1 X0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
  have l37 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l18 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l38 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0))))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l15 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) X0 (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)))]
  have l39 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l31 sK2 sK0 sK1]
    conv => enter [1]; rw [l14 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l34 sK1 X0]
  have l41 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l35 sK0 sK1 X0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1 sK0]
  have l43 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l29 X2 X0 X1 X1]
    conv => enter [1]; rw [← l37 X2 X0 X1]
  have l44 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l38 X1 sK1 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← l29 X1 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) X1]
  have l45 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l44 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l43 X1 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l46 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l40 sK1 sK1]
    conv => enter [1]; rw [← l3 sK1 sK1]
  have l47 : ∀ sK2 sK0 sK1 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [← l45 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l46 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l41 sK0 sK1 (sK0 ◇ sK1)]
  have l53 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [← h54241 X0 (sK0 ◇ sK1) X0]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [← l41 sK0 sK1 sK1]
  have l55 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l41 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l56 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l55 sK2 sK0 sK1]
    conv => enter [1]; rw [l16 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l54 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l28 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l60 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l61 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l56 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2]; rw [l57 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l30 sK0 sK1 sK0]
  have l64 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [l61 sK2 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 sK1]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l67 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l49 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l66 sK1 sK0]
  have l69 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1]
  have l70 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [l69 sK2 sK0 sK1]
  have l71 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h54241 (sK2 ◇ (sK0 ◇ sK1)) sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1)]
  have l72 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h54241 X1 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h54241 X0 sK1 sK1]
  have l73 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l72 X1 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l74 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l70 sK2 sK0 sK1]
    conv => enter [1]; rw [l71 sK2 sK0 sK1]
  have l75 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l73 X1 sK1 X0]
    conv => enter [1]; rw [← l17 (sK1 ◇ sK1) X1 X0]
  have l76 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l14 sK2 sK0 sK1 (sK1 ◇ sK1)]
  have l77 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l76 sK2 sK0 sK1]
    conv => enter [1]; rw [l47 sK2 sK0 sK1 sK1]
  have l78 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l77 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l79 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l46 sK1]
    conv => enter [1]; rw [← l78 sK2 sK0 sK1]
  have l80 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l79 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 sK2 sK0 sK1 sK1]
  have l81 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54241 X0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l62 sK0 sK1]
  have l82 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l81 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l83 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l82 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l67 X0 sK1 sK0]
  have l84 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l53 X0 sK0 sK1]
    conv => enter [1]; rw [l83 X0 sK0 sK1]
  have l85 : ∀ sK2 sK0 sK1 X0 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l64 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l86 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l85 sK2 sK0 sK1 X0]
  have l87 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l51 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54241 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l88 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l86 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l87 sK2 sK0 sK1]
  have l89 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l39 sK2 sK0 sK1]
    conv => enter [1]; rw [l88 sK2 sK0 sK1]
  have l90 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l70 sK2 sK0 sK1]
    conv => enter [1]; rw [l89 sK2 sK0 sK1]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h54241 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l59 sK0 sK1]
  have l92 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [h54241 X0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l91 sK0 sK1]
  have l93 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l92 X0 sK0 sK1]
    conv => enter [1]; rw [← l67 X0 sK1 sK0]
  have l94 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l70 sK2 sK0 sK1]
  have l95 : ∀ sK2 sK0 sK1 X0 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l70 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l96 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l95 sK2 sK0 sK1 X0]
  have l97 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l94 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK1 sK2 sK0 sK1]
  have l98 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l97 sK1 sK2 sK0]
  have l99 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l98 sK1 sK2 sK0]
    conv => enter [1]; rw [← h54241 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1 sK1]
  have l100 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l74 sK2 sK0 sK1]
    conv => enter [1]; rw [← l99 sK1 sK2 sK0]
  have l101 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l80 sK1 sK2 sK0]
    conv => enter [1]; rw [← l70 sK2 sK0 sK1]
  have l102 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l80 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 (sK1 ◇ sK1)]
  have l103 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l80 sK1 sK2 sK0]
  have l104 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1, 1]; rw [l80 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l105 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l104 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [← l96 sK2 sK0 sK1 X0]
  have l106 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l75 X0 sK1 sK1]
    conv => enter [1]; rw [← l103 X0 sK2 sK0 sK1]
  have l107 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l102 sK0 sK1 sK2]
    conv => enter [1]; rw [l84 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1]
  have l108 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l105 sK1 X0 sK2 sK0]
  have l109 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l64 sK2 sK0 sK1]
    conv => enter [1]; rw [← l107 sK0 sK1 sK2]
  have l110 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l109 sK2 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ sK1)]
  have l111 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l110 sK2 sK0 sK1]
  have l112 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l101 sK1 sK1 sK0]
    conv => enter [1]; rw [← l111 sK0 sK1 sK1]
  have l113 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l112 sK1 sK0]
  have l114 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l115 : ∀ sK2 sK0 sK1 X0 : G, (((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l90 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l116 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l115 sK2 sK0 sK1 X0]
  have l117 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l108 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l116 sK2 sK0 sK1 X0]
  have l118 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l114 sK0 sK1 X0]
    conv => enter [1]; rw [l117 sK1 X0 sK2 sK0]
  have l119 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l101 sK1 sK2 sK0]
  have l120 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l119 sK1 sK2 sK0]
  have l121 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l120 sK1 sK2 sK0]
  have l122 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54241 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l121 sK1 sK2 sK0]
  have l123 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l46 sK1]
    conv => enter [1]; rw [l122 sK1 sK2 sK0]
  have l124 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [l123 sK1 sK2 sK0]
  have l125 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l124 sK0 sK1 sK2]
    conv => enter [1]; rw [← l100 sK2 sK0 sK1]
  have l126 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54241 (sK0 ◇ sK1) sK1 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2]
  have l127 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l126 sK0 sK1 sK2]
    conv => enter [1]; rw [← l118 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK2]
  have l128 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l127 sK0 sK1 sK2]
  have l129 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [l128 sK0 sK1 sK2]
  have l130 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l129 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK2 sK0 sK1]
  have l131 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [l130 sK2 sK0 sK1]
  have l132 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l101 sK1 sK2 sK0]
    conv => enter [1]; rw [l131 sK2 sK0 sK1]
  have l133 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [l132 sK1 sK2 sK0]
  have l134 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l133 sK0 sK1 sK2]
  have l135 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l134 X0 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l93 X0 sK0 sK1]
  have l136 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l106 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l135 X0 sK2 sK0 sK1]
  have l137 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l32 sK2 sK0 sK1 (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← h54241 X0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  have l138 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l32 sK2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l125 sK0 sK1 sK2]
  have l139 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l138 sK2 sK0 sK1]
  have l140 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l137 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) (X0 ◇ (sK1 ◇ sK1))]
  have l141 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l140 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l136 X0 sK1 sK2 sK0]
  have l142 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l139 sK0 sK1 sK0]
    conv => enter [1]; rw [l141 sK0 sK0 sK1 X0]
  have l143 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l142 sK0 sK1 X0]
    conv => enter [1]; rw [← h54241 X0 X0 (sK1 ◇ sK1)]
  have l144 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [l143 sK1 sK0 X0]
  have l145 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l144 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l146 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l145 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l147 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l27 X0 X1 X0 X1]
    conv => enter [1]; rw [← l146 sK0 sK1 X0 X1]
  have l148 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l147 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [h54241 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l148 x y z]

theorem Equation4512_54241_implies_Equation54177 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54177 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK0)]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK0)) X0]
  have l4 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l5 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (((sK2 ◇ sK0) ◇ X0) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h54241 X1 (sK1 ◇ sK1) ((sK2 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK2 sK0 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54241 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54241 sK1 X0 sK1]
  have l11 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l9 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l15 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0))))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [l5 X1 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) X0 (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)))]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1 X1]
    conv => enter [1]; rw [← l14 X2 X0 X1]
  have l18 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l15 X1 sK1 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← l11 X1 sK1 (sK1 ◇ (sK2 ◇ sK0)) X1]
  have l19 : ∀ X1 sK1 sK2 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 sK2 sK0
    conv => enter [1]; rw [l18 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l17 X1 sK1 (sK1 ◇ (sK2 ◇ sK0))]
  have l20 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l21 : ∀ sK2 sK0 X1 sK1 : G, ((sK2 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 X1 sK1
    conv => enter [1]; rw [← l19 X1 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l20 sK1]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h54241 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l23 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [l17 sK1 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54241 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l28 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1]
  have l31 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l4 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h54241 X0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK1]
  have l33 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l31 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK0]
  have l34 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l33 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK1 sK0]
  have l35 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l34 sK2 sK0 sK1]
    conv => enter [1]; rw [l21 sK2 sK0 sK1 sK1]
  have l36 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l35 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l37 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [← l36 sK2 sK0 sK1]
  have l38 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l30 sK0 sK1]
  have l39 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l38 X0 sK1 sK0]
    conv => enter [1]; rw [← l32 X0 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l41 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54241 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l40 sK0 sK1]
  have l42 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l41 X0 sK1 X0]
    conv => enter [1, 2]; rw [← l39 X0 sK1 X0]
  have l43 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ sK1)]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l43 sK1 sK2 sK0]
  have l45 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h54241 X0 sK1 sK1]
  have l46 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l42 X0 sK1]
    conv => enter [1]; rw [← l45 sK1 X0]
  have l47 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l39 sK2 sK1 sK0]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
    conv => enter [1]; rw [l47 sK2 sK0 sK1]
  have l49 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l46 sK2 sK1]
    conv => enter [1]; rw [h54241 sK1 sK2 sK0]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [l49 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l50 x y z]

theorem Equation4512_54241_implies_Equation54275 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation54275 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l3 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ X0) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [h54241 X1 (sK1 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK0 X0]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h54241 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK2 sK1]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54241 sK1 X0 sK1]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l7 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l13 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l3 X1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 X0]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1 X1]
    conv => enter [1]; rw [← l12 X2 X0 X1]
  have l16 : ∀ X1 sK1 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l13 X1 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← l9 X1 sK1 (sK1 ◇ sK0) X1]
  have l17 : ∀ X1 sK1 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1 sK0
    conv => enter [1]; rw [l16 X1 sK1 sK0]
    conv => enter [1, 2]; rw [l15 X1 sK1 (sK1 ◇ sK0)]
  have l18 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1 sK1]
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l19 : ∀ sK0 X1 sK1 : G, (sK0 ◇ (X1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [← l17 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← l18 sK1]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l1 sK1 ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK2 sK1]
  have l21 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK2 sK1]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [h54241 sK1 (sK2 ◇ (sK1 ◇ sK1)) (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l10 sK2 sK1]
  have l23 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [l21 sK1 sK2]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ sK1) (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l20 sK1 sK2]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [l23 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54241 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [l25 sK1 sK2]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [l26 sK1 sK2]
  have l28 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1, 2]; rw [← l22 sK2 sK1]
  have l29 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [h54241 X0 (sK2 ◇ (sK1 ◇ sK1)) (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l22 sK2 sK1]
  have l30 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54241 X0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l28 sK2 sK1]
  have l31 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l30 X0 sK1 sK2]
    conv => enter [1]; rw [← l29 X0 sK2 sK1]
  have l32 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l23 sK1 sK2]
  have l33 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [← l32 sK2 sK1]
  have l34 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [← l33 sK2 sK1]
  have l35 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l34 sK2 sK1]
    conv => enter [1]; rw [← l19 sK0 sK2 sK1]
  have l36 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l35 sK2 sK1 sK0]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54241 sK0 sK1 sK0]
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l37 z y x]

theorem Equation4512_54241_implies_Equation53855 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54241 : Equation54241 G) : Equation53855 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l6 sK1]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l9 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (((sK1 ◇ sK1) ◇ X0) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h54241 X1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2]; rw [l3 sK1 X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54241 X1 X2 X0]
    conv => enter [1]; rw [h54241 X1 X2 X2]
    conv => enter [1, 2]; rw [h54241 X1 X2 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54241 X2 X0 (X1 ◇ X2)]
    conv => enter [1, 2]; rw [← h54241 X0 X1 X2]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = (X0 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [h54241 sK3 (sK0 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h4512 sK3 (sK0 ◇ sK2) X0]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = (X1 ◇ (X2 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54241 (X1 ◇ X2) X3 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ X3)]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ (X1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54241 X0 X1 sK1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54241 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK1 X0 X1 : G, (sK1 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54241 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))]
  have l20 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l16 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [l15 sK1 X0]
  have l22 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [l14 sK3 sK0 sK2 X0]
  have l23 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l13 sK1 X0]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l25 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l26 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l9 X1 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))]
  have l27 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [l21 sK1 X0]
  have l28 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l6 sK1]
    conv => enter [1]; rw [l23 sK1 X0]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l24 sK1 X0]
  have l30 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l20 X2 X0 X1 X1]
    conv => enter [1]; rw [← l25 X2 X0 X1]
  have l31 : ∀ X1 sK1 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X1 sK1
    conv => enter [1]; rw [l26 X1 sK1 X1]
    conv => enter [1, 2]; rw [← l20 X1 sK1 (sK1 ◇ (sK1 ◇ sK1)) X1]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1 sK1]
    conv => enter [1]; rw [← l28 sK1 sK1]
  have l33 : ∀ X1 sK1 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1
    conv => enter [1]; rw [l31 X1 sK1]
    conv => enter [1, 2]; rw [l30 X1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l34 : ∀ X1 sK1 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1
    conv => enter [1]; rw [l33 X1 sK1]
    conv => enter [1]; rw [l17 sK1 X1 sK1]
  have l35 : ∀ X1 sK1 : G, (X1 ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X1 sK1
    conv => enter [1]; rw [h54241 X1 sK1 sK1]
    conv => enter [1]; rw [← l34 X1 sK1]
  have l36 : ∀ X1 sK1 : G, (X1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1
    conv => enter [1]; rw [l35 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l37 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l38 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54241 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l29 sK1 X0]
  have l39 : ∀ X0 sK1 X1 : G, (X0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 ((sK1 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l29 sK1 X0]
  have l40 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l39 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l41 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l38 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l42 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l36 X0 sK1]
    conv => enter [1]; rw [← l41 X0 sK1]
  have l43 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [← l42 X0 sK1]
  have l44 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ sK1) X1]
    conv => enter [1]; rw [← l43 X0 sK1 X1]
  have l45 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h54241 X1 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h54241 X0 sK1 sK1]
  have l46 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l45 X1 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))]
  have l47 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l46 X1 sK1 X0]
    conv => enter [1]; rw [← l10 (sK1 ◇ sK1) X1 X0]
  have l48 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((X0 ◇ X1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h54241 (X0 ◇ X1) sK1 (sK1 ◇ sK1)]
  have l49 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l48 sK1 X0 X1]
  have l50 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l49 X0 X1 sK1]
    conv => enter [1, 2, 2]; rw [← l42 X1 sK1]
  have l51 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l47 X0 sK1 X1]
    conv => enter [1]; rw [← l50 X0 X1 sK1]
  have l52 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK3 sK0 sK2 ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l29 sK1 (sK3 ◇ (sK0 ◇ sK2))]
  have l53 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (X0 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [h54241 X0 (sK3 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l22 sK3 sK0 sK2 X0]
  have l54 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l29 sK1 ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l22 sK3 sK0 sK2 (sK1 ◇ sK1)]
  have l55 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l22 sK3 sK0 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l8 sK1 ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1))]
  have l56 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l47 (sK1 ◇ (sK1 ◇ sK1)) sK1 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l55 sK1 sK3 sK0 sK2]
  have l57 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l54 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ sK1) ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))]
  have l58 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK1 ◇ sK1) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l52 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK3 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK1))]
  have l59 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l6 sK1]
    conv => enter [1]; rw [l56 sK1 sK3 sK0 sK2]
  have l60 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l57 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l40 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
  have l61 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l58 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← h54241 (sK3 ◇ (sK0 ◇ sK2)) sK1 (sK1 ◇ sK1)]
  have l62 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1]; rw [l59 sK1 sK3 sK0 sK2]
  have l63 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l62 sK1 sK3 sK0 sK2]
    conv => enter [1, 2]; rw [l61 sK3 sK0 sK2 sK1]
  have l64 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l63 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l18 sK1 (sK3 ◇ (sK0 ◇ sK2))]
  have l65 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l64 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [l53 sK1 sK3 sK0 sK2]
  have l66 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l65 sK1 sK3 sK0 sK2]
    conv => enter [1, 2]; rw [l61 sK3 sK0 sK2 sK1]
  have l67 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l66 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← h54241 (sK3 ◇ (sK0 ◇ sK2)) sK1 sK1]
  have l68 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l37 sK1]
    conv => enter [1]; rw [l67 sK1 sK3 sK0 sK2]
  have l69 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54241 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l60 sK1 sK0 sK2]
  have l70 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l69 X0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l42 X0 sK1]
  have l71 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l70 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l51 (sK0 ◇ sK2) sK1 X0]
  have l72 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l44 X0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l71 X0 sK1 sK0 sK2]
  have l73 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l32 sK1]
    conv => enter [1]; rw [l72 X0 sK1 sK0 sK2]
  have l74 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l37 sK1]
    conv => enter [1]; rw [l73 X0 sK1 sK0 sK2]
  have l75 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l68 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l22 sK3 sK0 sK2 (sK1 ◇ sK1)]
  have l76 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l32 sK1]
    conv => enter [1]; rw [l75 sK1 sK3 sK0 sK2]
  have l77 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l37 sK1]
    conv => enter [1]; rw [l76 sK1 sK3 sK0 sK2]
  have l78 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l77 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [l22 sK1 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l77 sK1 sK1 sK0 sK2]
  have l79 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l78 sK1 sK0 sK2]
    conv => enter [1]; rw [← l42 (sK0 ◇ sK2) sK1]
  have l80 : ∀ sK1 X0 sK0 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1, 2, 2]; rw [l79 sK1 sK0 sK2]
    conv => enter [1]; rw [← h54241 X0 (sK0 ◇ sK2) (sK1 ◇ sK1)]
  have l81 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h54241 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l80 sK1 X0 sK0 sK2]
  have l82 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l42 X0 sK1]
    conv => enter [1]; rw [l74 X0 sK1 sK0 sK2]
  have l83 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h54241 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l74 X1 sK1 sK0 sK2]
  have l84 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l83 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← l19 sK1 X0 (sK0 ◇ sK2)]
  have l85 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l79 sK1 sK1 sK1]
    conv => enter [1]; rw [← l82 X0 sK1 sK1 sK1]
  have l86 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l84 X0 X1 sK1 X0 X0]
    conv => enter [1, 2]; rw [← l81 X0 sK1 X0 X0]
  have l87 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l86 X0 X1 sK1]
    conv => enter [1]; rw [← h54241 X0 sK1 sK1]
  have l88 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l87 X0 X1 sK1]
    conv => enter [1]; rw [← l85 sK1 X0]
  have l89 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l88 X0 sK0 sK1]
    conv => enter [1]; rw [h54241 X0 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l89 x y z w]

end Semigroup5
