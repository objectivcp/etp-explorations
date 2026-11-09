import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54053_implies_Equation54145 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54053 : Equation54053 G) : Equation54145 G := by
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
  have l23 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← h54053 X0 X1 X2]
    conv => enter [1]; rw [l20 X0 X1]
  have l24 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← l17 X0 (X0 ◇ X1) X1 X1]
  have l25 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l26 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l25 X0 X1 X2]
    conv => enter [1]; rw [← l17 X0 X0 X1 X1]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l26 X0 X1 X2]
  have l28 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0 X1 X0]
    conv => enter [1]; rw [l27 X0 X1 X1]
  have l29 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l22 X1 X2 X0]
    conv => enter [1]; rw [l28 X1 X0]
  have l30 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l28 X1 X0]
  have l31 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l30 X1 X0 X2]
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
  have l34 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l23 (X1 ◇ X2) X2 X1]
    conv => enter [1]; rw [l29 (X1 ◇ X2) X2 X0]
  intro x y z w
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l34 x w z]
  conv => enter [1]; rw [l33 w z x]

theorem Equation4512_54145_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54145 : Equation54145 G) : Equation54053 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54145 X0 X1 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 X0]
  have l2 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l1 X0 X1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) X0]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK2 ◇ sK0)) sK2 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l2 (sK2 ◇ sK0) (sK1 ◇ sK0) sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 X2 X3 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (X2 ◇ (X3 ◇ (X2 ◇ X0))) := by
    intro sK0 sK2 X0 X2 X3
    conv => enter [1]; rw [← l2 X0 sK0 sK0 sK2]
    conv => enter [1]; rw [h54145 X0 sK0 X2 X3]
  have l6 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h54145 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [l2 X0 X2 sK0 sK2]
  have l7 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X2) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l2 X0 X1 sK0 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) sK0 sK2]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (X0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [l2 (sK2 ◇ sK0) X0 sK0 sK2]
  have l10 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [l7 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) X0 X2]
  have l11 : ∀ sK0 sK2 X0 X2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (X2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0 X2
    conv => enter [1]; rw [← l2 X0 sK0 sK0 sK2]
    conv => enter [1]; rw [l6 X0 sK0 X2 sK0 sK2]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l9 sK0 sK2 (sK2 ◇ sK0)]
  have l13 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l10 X0 X1 X2 sK0 sK2]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l11 sK0 sK2 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [← l12 sK0 sK2]
  have l15 : ∀ sK0 sK2 X2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro sK0 sK2 X2 X0
    conv => enter [1]; rw [l5 sK0 sK2 X2 X0 sK0]
    conv => enter [1]; rw [l13 X0 sK0 X2 sK0 sK2]
  have l16 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l17 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK0 sK2]
    conv => enter [1, 2]; rw [← l2 sK0 sK2 sK0 sK2]
  have l19 : ∀ sK0 X0 sK2 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [h54145 sK0 X0 (sK0 ◇ (sK2 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK2 sK0 sK2]
  have l20 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l19 sK0 X0 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l21 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 X0 sK2]
  have l22 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l21 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK2 sK0 sK2]
  have l23 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l22 sK2 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK2 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 sK2 sK0 sK2]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l26 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [← l25 sK1 sK0 sK2]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1, 1]; rw [l24 sK0 sK0 sK1]
  have l28 : ∀ sK0 X1 sK2 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X1 sK2 X0
    conv => enter [1, 2, 2]; rw [l18 sK0 sK2]
    conv => enter [1]; rw [← h54145 (sK0 ◇ (sK2 ◇ sK0)) X0 sK0 X1]
  have l29 : ∀ sK0 X1 sK2 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l28 sK0 X1 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 sK2 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l30 : ∀ sK2 sK0 sK1 X1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 X1 sK2]
  have l31 : ∀ sK2 sK0 sK1 X1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l30 sK2 sK0 sK1 X1]
    conv => enter [1, 2, 2]; rw [l24 sK0 sK2 sK1]
  have l32 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l23 sK0 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK0 sK1 X1]
  have l33 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1 X1]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l17 sK1 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 sK2]
  have l35 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK2 sK0 sK2]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK2 sK1]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l26 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1 sK0]
    conv => enter [1]; rw [l37 sK0 sK1 sK0]
  have l39 : ∀ sK1 sK0 X1 X2 X0 : G, ((sK1 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ sK0))) = (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1 X2 X0
    conv => enter [1]; rw [h54145 (sK1 ◇ sK0) X1 X2 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h54145 (sK1 ◇ sK0) X2 sK0 X0]
  have l40 : ∀ X2 sK0 sK1 X1 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro X2 sK0 sK1 X1
    conv => enter [1, 2]; rw [l33 sK0 sK1 X2]
    conv => enter [1]; rw [← l39 sK1 sK0 X1 X2 X2]
  have l41 : ∀ X2 sK0 sK1 sK2 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro X2 sK0 sK1 sK2
    conv => enter [1]; rw [l40 X2 sK0 sK1 X2]
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) X2 sK0 sK2]
  have l42 : ∀ sK0 sK1 X2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X2
    conv => enter [1, 1]; rw [l24 sK0 sK1 sK0]
    conv => enter [1]; rw [← l41 X2 sK0 sK1 sK0]
  have l43 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1 X2]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l44 x y z]

theorem Equation4512_54053_implies_Equation54126 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54053 : Equation54053 G) : Equation54126 G := by
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
  intro x y z
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [← l20 x (((((z ◇ z) ◇ z) ◇ z) ◇ z) ◇ z)]
  conv => enter [1, 2]; rw [← h4512 ((((z ◇ z) ◇ z) ◇ z) ◇ z) z x]
  conv => enter [1, 2]; rw [← h4512 (((z ◇ z) ◇ z) ◇ z) z (z ◇ x)]
  conv => enter [1, 2]; rw [← h4512 ((z ◇ z) ◇ z) z (z ◇ (z ◇ x))]
  conv => enter [1, 2]; rw [← h4512 (z ◇ z) z (z ◇ (z ◇ (z ◇ x)))]
  conv => enter [1, 2]; rw [← h4512 z z (z ◇ (z ◇ (z ◇ (z ◇ x))))]
  conv => enter [1]; rw [← l17 z x (z ◇ (z ◇ (z ◇ x))) z]
  conv => enter [1, 2]; rw [← l17 z x (z ◇ x) z]
  conv => enter [1]; rw [← l17 z z (z ◇ x) x]
  conv => enter [1]; rw [← l17 z z x z]

theorem Equation4512_54126_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54126 : Equation54126 G) : Equation54053 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54126 (sK1 ◇ sK0) (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 sK2 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h54126 (sK1 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [h54126 (sK1 ◇ sK0) sK0 X0]
  have l5 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54126 (sK1 ◇ sK0) sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54126 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK0 sK1]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54126 sK0 X0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0 X0]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0 sK1 X0]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54126 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l13 sK1 sK0 (sK1 ◇ sK0)]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK1 sK0 sK2]
  have l17 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l15 sK0 X0 sK1]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l18 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l16 sK1 sK0 sK2]
    conv => enter [1]; rw [← l17 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [← l18 y x z y]

theorem Equation4512_54055_implies_Equation54082 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54055 : Equation54055 G) : Equation54082 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54055 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54055 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (X0 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54055 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X0)]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X0)]
  have l6 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK1 sK2]
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l8 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l8 sK2 sK1 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [l9 sK2 sK1 sK0]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l13 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK2 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 X0]
  have l14 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ X0) (sK2 ◇ sK1) X1]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 X0]
  have l15 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 sK1 sK2 X0]
  have l16 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l15 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l14 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l18 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK1]
    conv => enter [1]; rw [l13 sK2 sK1 sK1]
  have l19 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK1 sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l20 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l17 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l21 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l18 sK1 sK2]
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
  have l22 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l16 sK1 sK2 ((X1 ◇ X1) ◇ X0) X0]
  have l23 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l20 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← l16 sK1 sK2 (X1 ◇ X1) X0]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [← l21 sK2 sK1 sK1]
  have l25 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l22 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X0]
  have l26 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
    conv => enter [1]; rw [← l23 X0 sK1 sK2 sK2]
  have l27 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [l26 sK2 sK1 X0]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2]
  have l30 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
    conv => enter [1]; rw [l29 sK1 sK2]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [l30 sK2 sK1 sK1]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← l32 sK2 sK1]
  have l34 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l35 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 X1]
    conv => enter [1, 2]; rw [← l27 sK1 sK2 X0]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l0 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l37 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [← l34 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l38 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l35 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l39 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l38 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← l28 sK1 sK2]
  have l40 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← l39 X0 sK1 sK2 X1]
  have l41 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l40 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (X1 ◇ X1)]
  have l42 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l7 X0 X0 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l43 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l42 X0 sK1 sK2]
  have l44 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54055 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l37 sK1 sK2]
  have l45 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l44 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l43 sK1 sK2 X0]
  have l46 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l45 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2 X1]
  have l47 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h54055 sK3 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l47 x y y z w]

theorem Equation4512_54082_implies_Equation54055 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54082 : Equation54082 G) : Equation54055 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54082 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54082 X2 X1 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h54082 X0 X1 (sK1 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54082 X0 sK1 sK0 sK2]
  have l3 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l2 sK1 sK0 sK2 X0]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK0 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1 sK0 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_54055_implies_Equation54089 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54055 : Equation54055 G) : Equation54089 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [← h54055 (X0 ◇ (X2 ◇ X2)) X1 X3]
    conv => enter [1, 2]; rw [← h54055 X0 X1 X2]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54055 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54055 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54055 X0 X2 X0]
    conv => enter [1, 2]; rw [h54055 X0 X0 X1]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54055 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54055 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [h54055 (X1 ◇ X1) X0 X2]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54055 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X0)]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54055 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ X0)]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54055 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ X0)]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0 sK1]
    conv => enter [1]; rw [← h54055 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ X2)]
  have l14 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ X2) (X0 ◇ (X1 ◇ X0))]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54055 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 X1]
    conv => enter [1]; rw [← l13 X0 X1 X1]
  have l17 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l14 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (X0 ◇ (X1 ◇ X0))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X0]
  have l20 : ∀ X0 X2 X1 X3 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [← l17 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X2) (X3 ◇ X3)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l22 : ∀ X0 X2 X1 X3 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l20 X0 X2 X1 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X2 (X3 ◇ X3)]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l22 X0 X2 X1 X0]
    conv => enter [1, 2]; rw [← l6 X2 X0 X0]
  have l24 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 X0]
  have l25 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ X0) (sK1 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 X0]
  have l26 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l10 sK0 sK1 X0]
  have l27 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l26 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l28 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l25 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54055 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK0 sK0]
  have l30 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← l28 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54055 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l32 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l30 X0 sK0 sK1 X1]
    conv => enter [1]; rw [← l27 sK0 sK1 (X1 ◇ X1) X0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l31 sK1 sK0]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK1]
    conv => enter [1]; rw [← l32 X0 sK0 sK1 sK1]
  have l35 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l34 sK1 sK0 X0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK1)]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1 sK1]
    conv => enter [1]; rw [h54055 (sK1 ◇ sK1) (sK1 ◇ sK0) sK1]
  have l40 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54055 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [h54055 (sK1 ◇ sK1) X0 sK1]
  have l41 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [← h54055 X1 X0 X2]
    conv => enter [1]; rw [h54055 X1 X0 sK1]
  have l42 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (sK1 ◇ sK1)) sK1]
  have l43 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h54055 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l44 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l43 sK1]
  have l45 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK1 ◇ sK1) X0]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ sK1)]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h54055 (sK1 ◇ sK0) sK0 sK1]
  have l48 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l44 sK1]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l45 sK0 sK1 X0]
    conv => enter [1]; rw [← l27 sK0 sK1 ((sK1 ◇ sK1) ◇ X0) X0]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l46 sK1 sK0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK1)]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l50 sK0 sK1]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK1) X0]
  have l54 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 sK1 X0]
    conv => enter [1]; rw [← l53 sK0 sK1 X0]
  have l55 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h54055 X0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l56 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l55 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l54 sK0 sK1 X0]
  have l57 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK1 ◇ sK1) sK1 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 (sK1 ◇ sK1)]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0]
    conv => enter [1]; rw [← l40 sK1 sK1]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l60 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1]
    conv => enter [1]; rw [← l62 sK1 sK0]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l63 sK1 sK0]
    conv => enter [1]; rw [l52 sK1 sK0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1 sK0]
    conv => enter [1]; rw [← l64 sK1 sK0]
  have l66 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54055 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l56 sK0 sK1 X0]
    conv => enter [1]; rw [← l66 sK1 X0 sK0]
  have l68 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l69 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l70 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l69 X0 X1 X2]
  have l71 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l67 sK0 sK1 X0]
    conv => enter [1]; rw [l68 sK1 X0]
  have l72 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X0 ◇ (X0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l71 sK0 sK1 (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l19 X0 (sK1 ◇ sK1)]
  have l73 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l72 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ sK1)) (X0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l74 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l73 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) (X0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l75 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l74 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 X0 X0 (sK1 ◇ sK1) X0]
  have l76 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l75 sK0 sK1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l77 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l76 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))]
  have l78 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l77 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))]
  have l79 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l78 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l23 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l80 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l79 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l81 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l80 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ (X0 ◇ X1))]
  have l82 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l81 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l70 X1 X0 X1]
  have l83 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l82 sK0 sK1 X1 X0]
    conv => enter [1]; rw [l41 X1 X0 X1 sK1]
  intro x y z
  conv => enter [1]; rw [l83 x y z x]

theorem Equation4512_54089_implies_Equation54055 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54089 : Equation54089 G) : Equation54055 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54089 sK0 sK2 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  have l2 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
    conv => enter [1]; rw [h54089 sK0 sK2 X0]
  have l3 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [h54089 X0 (sK0 ◇ (sK2 ◇ sK2)) X1]
    conv => enter [1, 2, 2]; rw [l2 (sK0 ◇ (sK2 ◇ sK2)) sK0 sK2 sK1]
  have l4 : ∀ sK1 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK0 sK2 X1 X0
    conv => enter [1, 1]; rw [l2 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK2 ◇ sK2)) X1]
  have l5 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK0 sK2 X0 sK1]
  have l7 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 sK2 X0 X0]
    conv => enter [1]; rw [l3 X0 sK0 sK2 X1 sK1]
  have l8 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (X1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← l6 sK1 sK0 sK2 X0]
  have l9 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0 sK2 X0 sK1]
  have l10 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h54089 X0 X1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l9 sK1 sK0 sK2 (X0 ◇ (X1 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [l10 x y y x z]

theorem Equation4512_54055_implies_Equation54099 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54055 : Equation54055 G) : Equation54099 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54055 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (X0 ◇ X0)]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54055 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
    conv => enter [1]; rw [← l0 sK2 sK1 (X0 ◇ X0)]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1]
    conv => enter [1]; rw [← h54055 (sK2 ◇ sK1) (sK2 ◇ sK1) sK1]
  have l6 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l7 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l5 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l8 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l7 sK2 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK2 sK1]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l9 sK1 sK2]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l12 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ X0) (sK2 ◇ sK1) X1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 X0]
  have l13 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l3 sK1 sK2 X0]
  have l14 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l13 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l15 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l12 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l16 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK1 sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l17 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l15 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l18 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l16 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l14 sK1 sK2 ((X1 ◇ X1) ◇ X0) X0]
  have l19 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l14 sK1 sK2 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l17 X0 sK1 sK2 X1]
  have l20 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l18 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X0]
  have l21 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK1 sK2]
    conv => enter [1]; rw [l19 sK1 sK2 sK2 X0]
  have l22 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l21 sK2 sK1 X0]
  have l23 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ sK0)]
  have l24 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 X1]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 X0]
  have l25 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l24 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l26 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l25 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [l10 sK1 sK2]
  have l27 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l26 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (X1 ◇ X1)]
  have l28 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l27 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l6 X0 X0 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l28 X0 sK1 sK2]
  have l30 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54055 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l10 sK1 sK2]
  have l31 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l30 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l29 sK1 sK2 X0]
  have l32 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1]
    conv => enter [1, 2]; rw [← l23 sK1 sK2 sK1]
  have l33 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l29 sK1 sK2 X0]
    conv => enter [1]; rw [← l32 sK1 sK2 X0]
  have l34 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l31 sK1 X0 sK1 sK2]
    conv => enter [1]; rw [h54055 sK1 X0 sK0]
  have l35 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l33 sK1 sK2 X0]
    conv => enter [1]; rw [l31 (sK1 ◇ (sK2 ◇ sK1)) X0 sK1 sK2]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK3]
    conv => enter [1]; rw [l34 sK3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l36 x y z w]

@[equational_result]
theorem Equation54099_implies_Equation54055 (G : Type*) [Magma G] (h54099 : Equation54099 G) : Equation54055 G := by
  intro x y z
  conv => enter [1]; rw [h54099 x y y z]

theorem Equation4512_54055_implies_Equation54116 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54055 : Equation54055 G) : Equation54116 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54055 sK1 X0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54055 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (X0 ◇ X0)]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54055 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X0)]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X0)]
  have l6 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK1 sK2]
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l8 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l8 sK2 sK1 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2]
    conv => enter [1]; rw [l9 sK2 sK1 sK0]
  have l11 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l13 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK2 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 X0]
  have l14 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ X0) (sK2 ◇ sK1) X1]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 X0]
  have l15 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 sK1 sK2 X0]
  have l16 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l15 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l14 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l18 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK1]
    conv => enter [1]; rw [l13 sK2 sK1 sK1]
  have l19 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK1 sK2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l20 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l17 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l21 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l18 sK1 sK2]
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
  have l22 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l16 sK1 sK2 ((X1 ◇ X1) ◇ X0) X0]
  have l23 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l20 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← l16 sK1 sK2 (X1 ◇ X1) X0]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [← l21 sK2 sK1 sK1]
  have l25 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l22 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X0]
  have l26 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
    conv => enter [1]; rw [← l23 X0 sK1 sK2 sK2]
  have l27 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [l26 sK2 sK1 X0]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2]
  have l30 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
    conv => enter [1]; rw [l29 sK1 sK2]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [l30 sK2 sK1 sK1]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← l32 sK2 sK1]
  have l34 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l33 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l35 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 X1]
    conv => enter [1, 2]; rw [← l27 sK1 sK2 X0]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l0 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l37 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [← l34 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l38 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l35 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l39 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l38 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← l28 sK1 sK2]
  have l40 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← l39 X0 sK1 sK2 X1]
  have l41 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l40 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (X1 ◇ X1)]
  have l42 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK1 sK2 X0]
    conv => enter [1]; rw [l7 X0 X0 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l43 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l42 X0 sK1 sK2]
  have l44 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54055 X0 X1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l37 sK1 sK2]
  have l45 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l44 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l43 sK1 sK2 X0]
  have l46 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l45 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2 X1]
  have l47 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l46 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [h54055 sK2 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l47 x y z w]

theorem Equation4512_54116_implies_Equation54055 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54116 : Equation54116 G) : Equation54055 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ sK2 X0 X1 : G, ((sK2 ◇ X0) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h54116 (sK2 ◇ X0) sK2 X1 sK2]
  have l5 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h54116 (sK2 ◇ sK2) (sK1 ◇ sK0) X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l6 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h54116 sK0 (sK1 ◇ sK0) X0 sK2]
  have l7 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54116 X0 sK0 sK1 sK2]
  have l8 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54116 X0 (sK0 ◇ (sK2 ◇ sK2)) sK1 sK2]
  have l9 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X0))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1, 2]; rw [h54116 X0 X1 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 (X1 ◇ (sK2 ◇ sK2))]
  have l10 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (X1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54116 X0 X1 sK2 sK2]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54116 X0 (sK2 ◇ sK2) (sK0 ◇ (sK1 ◇ sK0)) sK2]
  have l12 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l10 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK2 X0 X1]
  have l13 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l7 sK1 sK0 sK2 X0]
  have l14 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l15 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [← l4 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK2 X0 ((sK2 ◇ sK2) ◇ X0)]
  have l16 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← h54116 (sK0 ◇ (sK2 ◇ sK2)) sK1 X0 sK2]
    conv => enter [1]; rw [← l5 sK2 sK1 sK0 (sK0 ◇ (sK2 ◇ sK2))]
  have l17 : ∀ X1 sK2 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X1 sK2
    conv => enter [1]; rw [l15 X1 sK2 X1]
    conv => enter [1]; rw [← l10 sK2 (sK2 ◇ sK2) X1]
  have l18 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l14 sK0 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l16 X0 sK1 sK2 sK0]
  have l19 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l17 X1 sK2]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54116 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l18 sK0 sK1 sK0 sK0]
  have l21 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h54116 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 sK2]
  have l22 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X1 X0
    conv => enter [1, 2]; rw [h54116 (sK2 ◇ sK2) sK0 X0 sK2]
    conv => enter [1]; rw [h54116 (sK0 ◇ (sK2 ◇ sK2)) X0 X1 sK2]
  have l23 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK2 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l22 sK0 sK2 X1 X0]
  have l24 : ∀ sK2 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l21 sK2 sK2 sK2]
    conv => enter [1]; rw [l23 sK2 sK2 sK2 X1 X0]
  have l25 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (((sK2 ◇ sK2) ◇ X0) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK0 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK2) X0]
  have l26 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [l13 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [h54116 sK1 sK0 X1 sK2]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l24 sK2 sK1 sK0]
  have l28 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) X0 ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l29 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l28 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [← l12 sK2 (sK0 ◇ (sK2 ◇ sK2)) sK1]
  have l30 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK0 sK2]
    conv => enter [1]; rw [← l8 sK1 sK0 sK2 (sK2 ◇ sK2)]
  have l31 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l27 sK1 sK0 sK2]
  have l32 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l27 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [← l31 sK2 sK1 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK1 sK0 sK2 (sK2 ◇ sK2)]
  have l35 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l30 sK1 sK0 sK2]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l35 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

theorem Equation4512_54055_implies_Equation54141 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54055 : Equation54055 G) : Equation54141 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK2 sK1 X0]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = ((X0 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [← h54055 (X0 ◇ (X2 ◇ X2)) X1 X3]
    conv => enter [1, 2]; rw [← h54055 X0 X1 X2]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54055 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54055 X0 X2 X0]
    conv => enter [1, 2]; rw [h54055 X0 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54055 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [h54055 (X1 ◇ X1) X0 X2]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54055 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X0)]
  have l8 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X0)]
  have l9 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X1)))) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l0 sK2 sK1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (sK2 ◇ sK1) X1]
  have l10 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1 sK2]
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ X2)]
  have l12 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = (X0 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ X2) (X0 ◇ (X1 ◇ X0))]
  have l13 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0 X1]
    conv => enter [1]; rw [← l11 X0 X1 X1]
  have l15 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X3))) = (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l12 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (X0 ◇ (X1 ◇ X0))]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l13 sK2 sK1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X0]
  have l18 : ∀ X0 X2 X1 X3 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X3)))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [← l15 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X2) (X3 ◇ X3)]
  have l19 : ∀ X0 X2 X1 X3 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l18 X0 X2 X1 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X2 (X3 ◇ X3)]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l19 X0 X2 X1 X0]
    conv => enter [1, 2]; rw [← l5 X2 X0 X0]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l0 sK2 sK1 (sK2 ◇ sK1)]
  have l23 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l7 sK1 sK2 X0]
  have l24 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l23 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l25 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK2]
  have l26 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l21 sK1 sK2]
  have l27 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0))) = ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h54055 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l21 sK1 sK2]
  have l28 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l27 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l29 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
    conv => enter [1]; rw [l26 sK1 sK2]
  have l30 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ X0)]
    conv => enter [1]; rw [l28 sK2 sK1 X0]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l29 sK2 sK1]
    conv => enter [1, 2]; rw [l25 sK1 sK2]
  have l32 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X0)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK1 (X0 ◇ X0)]
    conv => enter [1]; rw [l30 sK2 sK1 X0]
  have l33 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l31 sK1 sK2]
  have l34 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l9 sK2 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l32 sK2 sK1 sK2]
  have l35 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l34 sK2 sK1]
  have l36 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l35 sK2 sK1]
  have l37 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h54055 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
    conv => enter [1]; rw [l36 sK1 sK2]
  have l38 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l16 sK2 sK1]
    conv => enter [1]; rw [l37 sK2 sK1]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [l38 sK2 sK1]
  have l40 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h54055 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) sK2 X0]
    conv => enter [1, 2]; rw [← l22 sK1 sK2]
  have l41 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) X0]
  have l42 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l41 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l43 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l40 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l44 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l43 sK2 sK1 X0]
    conv => enter [1]; rw [h54055 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) sK2]
  have l45 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l44 sK2 sK1 X0]
    conv => enter [1, 2]; rw [l25 sK1 sK2]
  have l46 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X0)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1]; rw [l45 sK2 sK1 X0]
  have l47 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l9 sK2 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l46 sK2 sK1 sK2]
  have l48 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l47 sK2 sK1]
  have l49 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l48 sK2 sK1]
  have l50 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l33 sK2 sK1]
  have l51 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l49 sK1 sK2]
    conv => enter [1]; rw [← l50 sK2 sK1]
  have l52 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l39 sK1 sK2]
    conv => enter [1]; rw [← l51 sK1 sK2]
  have l53 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1, 2]; rw [← l52 sK1 sK2]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1, 2]; rw [← l53 sK1 sK2]
  have l55 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l53 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l56 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l52 sK1 sK2]
    conv => enter [1]; rw [l54 sK1 sK2]
  have l57 : ∀ X0 X1 X2 sK2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 X2 sK2
    conv => enter [1]; rw [← h54055 X1 X0 X2]
    conv => enter [1]; rw [h54055 X1 X0 sK2]
  have l58 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (sK2 ◇ sK2)) sK2]
  have l59 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l58 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X0]
  have l60 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l59 sK1 sK2 X0]
    conv => enter [1]; rw [← l24 sK1 sK2 ((sK2 ◇ sK2) ◇ X0) X0]
  have l61 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l56 sK1 sK2]
    conv => enter [1]; rw [← l29 sK2 sK1]
  have l62 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l61 sK1 sK2]
    conv => enter [1]; rw [← l55 sK1 sK2 (sK2 ◇ sK2)]
  have l63 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l62 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK2) X0]
  have l64 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l60 sK1 sK2 X0]
    conv => enter [1]; rw [← l63 sK1 sK2 X0]
  have l65 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l64 sK1 sK2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← h54055 X0 (sK1 ◇ (sK2 ◇ sK1)) sK2]
  have l66 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l65 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l64 sK1 sK2 X0]
  have l67 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h54055 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l39 sK1 sK2]
  have l68 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l66 sK1 sK2 X0]
    conv => enter [1]; rw [← l67 sK2 X0 sK1]
  have l69 : ∀ sK2 X0 : G, (sK2 ◇ (X0 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l17 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l70 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l71 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l70 X0 X1 X2]
  have l72 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l68 sK1 sK2 X0]
    conv => enter [1]; rw [l69 sK2 X0]
  have l73 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ (X0 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l72 sK1 sK2 (X0 ◇ (X0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l17 X0 (sK2 ◇ sK2)]
  have l74 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l73 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK2 ◇ sK2)) (X0 ◇ ((sK2 ◇ sK2) ◇ X0))]
  have l75 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X0))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l74 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) (X0 ◇ ((sK2 ◇ sK2) ◇ X0))]
  have l76 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l75 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 X0 X0 (sK2 ◇ sK2) X0]
  have l77 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l76 sK1 sK2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l78 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l77 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))]
  have l79 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l78 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))]
  have l80 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l79 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l20 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l81 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l80 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X1 ◇ (X0 ◇ X1))]
  have l82 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l81 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ (X0 ◇ X1))]
  have l83 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l82 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l71 X1 X0 X1]
  have l84 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l83 sK1 sK2 X1 X0]
    conv => enter [1]; rw [l57 X1 X0 X1 sK2]
  intro x y z w
  conv => enter [1]; rw [l84 x y z w]

theorem Equation4512_54141_implies_Equation54055 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54141 : Equation54141 G) : Equation54055 G := by
  have l0 : ∀ X0 X1 sK2 X2 X3 : G, (X0 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X2 ◇ (X3 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2 X2 X3
    conv => enter [1]; rw [h54141 X0 (X1 ◇ (sK2 ◇ sK2)) X2 X3]
    conv => enter [1, 2, 2]; rw [← h54141 sK2 sK2 (X1 ◇ (sK2 ◇ sK2)) X1]
  have l1 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X2) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK2 ◇ sK2)) X2]
    conv => enter [1, 1]; rw [← h54141 sK2 sK2 X0 X1]
  have l2 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54141 sK2 sK2 sK1 sK0]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l2 sK1 sK0 sK2]
  have l4 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X2)) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [l1 X0 X1 sK2 X2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X2]
  have l5 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [l0 X0 X1 sK2 X2 X0]
    conv => enter [1, 2]; rw [← h54141 sK2 sK2 X0 sK2]
  have l6 : ∀ sK2 X2 X0 X1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X2)) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X2))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [← l4 X0 X1 sK2 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (sK2 ◇ sK2) X2]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((X1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h54141 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← l5 X0 X1 sK2 sK2]
  have l8 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l7 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK2 ◇ sK2) X0]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l8 sK2 X0 sK2]
    conv => enter [1]; rw [← l6 sK2 X0 X0 sK2]
  have l10 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 sK2 X0]
  have l11 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l3 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l12 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← l11 sK1 sK0 sK2 X0]
  have l13 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h54141 X0 X1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK2 (X0 ◇ (X1 ◇ X1))]
  intro x y z
  conv => enter [1]; rw [l13 x y y x z]

theorem Equation4512_54055_implies_Equation54159 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54055 : Equation54055 G) : Equation54159 G := by
  have l0 : ∀ sK3 sK2 X0 : G, ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ X0)) = (sK3 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← h4512 sK3 sK2 ((sK3 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ sK2) X0]
  have l1 : ∀ sK3 sK2 X0 X1 : G, (sK3 ◇ ((sK2 ◇ X0) ◇ (X1 ◇ X1))) = ((sK2 ◇ X0) ◇ ((sK3 ◇ sK2) ◇ X0)) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [← h54055 (sK2 ◇ X0) sK3 X1]
    conv => enter [1, 2]; rw [h4512 sK3 sK2 X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54055 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
  have l3 : ∀ sK3 sK2 X0 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [h54055 (sK3 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) (X0 ◇ X0)]
  have l4 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK3 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h54055 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK3 sK2 (X0 ◇ X0)]
  have l5 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2)))) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [h54055 (sK2 ◇ (sK3 ◇ sK2)) sK3 X0]
    conv => enter [1]; rw [← l0 sK3 sK2 (X0 ◇ X0)]
  have l6 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2)))) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l5 sK2 sK3 sK2]
    conv => enter [1]; rw [← h54055 (sK3 ◇ sK2) (sK3 ◇ sK2) sK2]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l8 : ∀ sK3 sK2 X0 X1 : G, (sK3 ◇ ((sK2 ◇ X0) ◇ (X1 ◇ X1))) = (sK2 ◇ (X0 ◇ ((sK3 ◇ sK2) ◇ X0))) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK2 X0 ((sK3 ◇ sK2) ◇ X0)]
  have l9 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [← l6 sK2 sK3]
    conv => enter [1, 2]; rw [h4512 sK3 sK2 (sK3 ◇ sK2)]
  have l10 : ∀ sK3 sK2 X0 X1 : G, (sK3 ◇ (sK2 ◇ (X0 ◇ (X1 ◇ X1)))) = (sK2 ◇ (X0 ◇ ((sK3 ◇ sK2) ◇ X0))) := by
    intro sK3 sK2 X0 X1
    conv => enter [1, 2]; rw [h4512 sK2 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l8 sK3 sK2 X0 X1]
  have l11 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l3 sK3 sK2 (sK3 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK3 sK2]
  have l12 : ∀ sK3 sK2 X0 X1 : G, ((sK3 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X1))) = (sK2 ◇ (X0 ◇ ((sK3 ◇ sK2) ◇ X0))) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK3 sK2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l10 sK3 sK2 X0 X1]
  have l13 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l4 sK2 sK3 (sK3 ◇ sK2)]
    conv => enter [1]; rw [← l11 sK3 sK2]
  have l14 : ∀ sK2 sK3 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK2) (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2]; rw [← l13 sK2 sK3]
  have l15 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK3 ◇ sK2) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l4 sK2 sK3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h54055 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l16 : ∀ sK3 sK2 X0 X1 : G, ((sK3 ◇ sK2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = ((X0 ◇ X0) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ X0) (sK3 ◇ sK2) X1]
    conv => enter [1, 2]; rw [← l4 sK2 sK3 X0]
  have l17 : ∀ sK3 sK2 X0 X1 : G, ((sK3 ◇ sK2) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ X1) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK2) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l4 sK2 sK3 X0]
  have l18 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ X1) = ((sK3 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [← l17 sK3 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l19 : ∀ sK3 sK2 X0 X1 : G, ((sK3 ◇ sK2) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 X0 X1
    conv => enter [1]; rw [l16 sK3 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (sK2 ◇ (sK3 ◇ sK2))]
  have l20 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK3 ◇ sK2) ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0)))) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l15 sK2 sK3 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l21 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) = ((sK3 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← l19 sK3 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l22 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((X1 ◇ X1) ◇ X0)) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l20 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l18 sK2 sK3 ((X1 ◇ X1) ◇ X0) X0]
  have l23 : ∀ sK2 sK3 X1 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l18 sK2 sK3 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l21 X0 sK2 sK3 X1]
  have l24 : ∀ sK2 sK3 X1 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK2 sK3 X1 X0
    conv => enter [1]; rw [l22 sK2 sK3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X0]
  have l25 : ∀ sK3 sK2 X0 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [l3 sK3 sK2 sK3]
    conv => enter [1]; rw [l23 sK2 sK3 sK3 X0]
  have l26 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l13 sK2 sK3]
    conv => enter [1]; rw [l25 sK3 sK2 X0]
  have l27 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ (X1 ◇ X1))) = ((X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← h54055 (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) X0 X1]
    conv => enter [1, 2]; rw [← l26 sK2 sK3 X0]
  have l28 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))))) := by
    intro sK3 sK2
    conv => enter [1, 2]; rw [l26 sK2 sK3 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [← l0 sK3 sK2 ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2)))]
  have l29 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (sK2 ◇ ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l28 sK3 sK2]
    conv => enter [1]; rw [l12 sK3 sK2 (sK3 ◇ sK2) (sK2 ◇ (sK3 ◇ sK2))]
  have l30 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ (X1 ◇ X1))) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [l27 X0 sK2 sK3 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK3 ◇ sK2)) (sK2 ◇ (sK3 ◇ sK2))]
  have l31 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l29 sK3 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK2) ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2))]
  have l32 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) ◇ (X1 ◇ X1))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [l30 X0 sK2 sK3 X1]
    conv => enter [1, 2]; rw [l14 sK2 sK3]
  have l33 : ∀ sK3 sK2 : G, (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l31 sK3 sK2]
    conv => enter [1]; rw [← l3 sK3 sK2 (sK3 ◇ sK2)]
  have l34 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2)))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X1 ◇ X1)))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1]; rw [← l32 X0 sK2 sK3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ (sK3 ◇ sK2)) (X1 ◇ X1)]
  have l35 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l13 sK2 sK3]
    conv => enter [1]; rw [← l33 sK3 sK2]
  have l36 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2)))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))))) := by
    intro X0 sK2 sK3
    conv => enter [1]; rw [l34 X0 sK2 sK3 X0]
    conv => enter [1]; rw [l7 X0 X0 (sK2 ◇ (sK3 ◇ sK2)) X0]
  have l37 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l24 sK2 sK3 X0 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [← l36 X0 sK2 sK3]
  have l38 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK3 ◇ sK2) ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l35 sK2 sK3]
    conv => enter [1]; rw [h4512 sK3 sK2 (sK3 ◇ sK2)]
  have l39 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ (sK3 ◇ sK2)) ◇ X0) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1, 1]; rw [l38 sK2 sK3]
    conv => enter [1]; rw [← h4512 (sK3 ◇ sK2) (sK3 ◇ sK2) X0]
  have l40 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2)))) = (sK3 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l0 sK3 sK2 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2]; rw [l14 sK2 sK3]
  have l41 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2))))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h54055 X0 X1 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l14 sK2 sK3]
  have l42 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l41 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [← l37 sK2 sK3 X0]
  have l43 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK3 ◇ sK2) ◇ ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2)))) := by
    intro sK3 sK2
    conv => enter [1]; rw [← h4512 sK3 sK2 (sK2 ◇ (sK3 ◇ sK2))]
    conv => enter [1]; rw [← l40 sK3 sK2]
  have l44 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l43 sK3 sK2]
    conv => enter [1]; rw [← l39 sK2 sK3 (sK2 ◇ (sK3 ◇ sK2))]
  have l45 : ∀ sK3 sK2 : G, ((sK3 ◇ sK2) ◇ (sK2 ◇ (sK3 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK3 sK2
    conv => enter [1]; rw [l44 sK3 sK2]
    conv => enter [1]; rw [l14 sK2 sK3]
  have l46 : ∀ sK2 sK3 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l13 sK2 sK3]
    conv => enter [1]; rw [l45 sK3 sK2]
  have l47 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l37 sK2 sK3 X0]
    conv => enter [1, 2]; rw [← l46 sK2 sK3]
  have l48 : ∀ X0 sK2 sK3 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l42 sK1 X0 sK2 sK3]
    conv => enter [1]; rw [h54055 sK1 X0 sK0]
  have l49 : ∀ sK2 sK3 X0 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK3 X0 sK1 sK0
    conv => enter [1]; rw [l47 sK2 sK3 X0]
    conv => enter [1]; rw [l48 X0 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l49 x y z w u]

theorem Equation4512_54159_implies_Equation54055 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54159 : Equation54159 G) : Equation54055 G := by
  have l0 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [h54159 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l1 : ∀ X0 X1 sK1 sK0 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK0 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK2 ◇ sK2)]
  have l2 : ∀ sK1 sK0 sK2 X2 X3 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (X2 ◇ (X3 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2 X2 X3
    conv => enter [1]; rw [← l1 sK1 sK1 sK1 sK0 sK2]
    conv => enter [1]; rw [h54159 sK1 sK1 X2 X3 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54159 sK0 sK1 sK0 sK0 sK2]
    conv => enter [1]; rw [l2 sK0 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation54160_implies_Equation54056 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54056 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54160 sK1 sK2 sK1 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h54160 X0 X1 sK1 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [h54160 sK1 sK1 X2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y y z w]

theorem Equation4512_54056_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54056 : Equation54056 G) : Equation54160 G := by
  have l0 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK4 ◇ ((sK3 ◇ X0) ◇ X1)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK4 sK3 X0]
    conv => enter [1]; rw [← h4512 sK4 (sK3 ◇ X0) X1]
  have l1 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK4 ◇ (sK3 ◇ (X0 ◇ X1))) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [l0 sK4 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK3 X0 X1]
  have l2 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (((sK4 ◇ sK3) ◇ X0) ◇ X1) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [h54056 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← l1 sK4 sK3 X0 X1]
  have l3 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l2 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← h4512 (sK4 ◇ sK3) X0 X1]
  have l4 : ∀ sK3 sK4 X0 X1 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK3) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l3 sK3 sK4 X0 X1]
  have l5 : ∀ sK4 sK3 X0 X1 X2 : G, ((sK4 ◇ sK3) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ X2) := by
    intro sK4 sK3 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK4 ◇ sK3) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l3 sK3 sK4 X0 X1]
  have l6 : ∀ sK3 sK4 X2 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ X2) := by
    intro sK3 sK4 X2
    conv => enter [1]; rw [l3 sK3 sK4 (sK3 ◇ sK3) X2]
    conv => enter [1]; rw [l5 sK4 sK3 sK3 sK3 X2]
  have l7 : ∀ sK3 sK4 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK4 sK0 sK1
    conv => enter [1, 2]; rw [l3 sK3 sK4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) (sK0 ◇ sK1)]
  have l8 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4
    conv => enter [1]; rw [l6 sK3 sK4 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l7 sK3 sK4 sK3 sK3]
  have l9 : ∀ sK3 sK4 X0 X1 X2 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK3 ◇ (X0 ◇ ((sK4 ◇ sK3) ◇ X0))) := by
    intro sK3 sK4 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK3) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h54056 X0 (sK4 ◇ sK3) X1 X2]
  have l10 : ∀ sK3 sK4 X0 X1 X2 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK4 X0 X1 X2
    conv => enter [1]; rw [l9 sK3 sK4 X0 X1 X2]
    conv => enter [1]; rw [← h54056 X0 sK3 (sK4 ◇ sK3) X0]
  have l11 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) = (X0 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← l4 sK3 sK4 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l10 sK3 sK4 X0 sK3 sK3]
  have l12 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l8 sK3 sK4]
    conv => enter [1]; rw [l11 sK3 sK4 X0]
  have l13 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK3 ◇ (X0 ◇ X1)))) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l12 sK3 sK4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK3 ◇ (X0 ◇ X1))]
  have l14 : ∀ sK3 sK4 X1 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [l13 sK3 sK4 X0 X1]
    conv => enter [1]; rw [← h54056 X1 X0 sK3 (X0 ◇ X1)]
  have l15 : ∀ sK3 sK4 X0 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X0 sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK3 sK4 sK2 X0]
    conv => enter [1]; rw [h54056 sK2 X0 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l15 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54070 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54070 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54160 sK1 sK2 sK1 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h54160 X0 X1 sK1 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (sK3 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [h54160 sK1 sK1 X2 sK3 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y y z w]

theorem Equation4512_54070_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54070 : Equation54070 G) : Equation54160 G := by
  have l0 : ∀ sK4 sK3 X1 X0 X2 : G, ((sK4 ◇ sK3) ◇ (X1 ◇ (X0 ◇ X2))) = (sK4 ◇ (X0 ◇ (sK3 ◇ X0))) := by
    intro sK4 sK3 X1 X0 X2
    conv => enter [1]; rw [← h4512 sK4 sK3 (X1 ◇ (X0 ◇ X2))]
    conv => enter [1, 2]; rw [← h54070 X0 sK3 X1 X2]
  have l1 : ∀ sK3 sK4 X1 X0 X2 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK4 ◇ sK3) ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK3 sK4 X1 X0 X2
    conv => enter [1]; rw [h54070 sK3 sK4 X0 X0]
    conv => enter [1]; rw [← l0 sK4 sK3 X1 X0 X2]
  have l2 : ∀ X0 X1 sK3 sK4 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro X0 X1 sK3 sK4
    conv => enter [1]; rw [h54070 X0 X1 (sK4 ◇ sK3) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 sK3 sK4 X0 X0 X0]
  have l3 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l1 sK3 sK4 X0 sK4 sK3]
    conv => enter [1]; rw [l2 (sK4 ◇ sK3) X0 sK3 sK4]
  have l4 : ∀ X0 sK3 sK4 sK2 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK4 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [← l2 sK0 X0 sK3 sK4]
    conv => enter [1]; rw [h54070 sK0 X0 sK2 sK1]
  have l5 : ∀ sK3 sK4 X0 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X0 sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK3 sK4 X0]
    conv => enter [1]; rw [l4 X0 sK3 sK4 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l5 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54083 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54083 G := by
  intro x y z w u
  conv => enter [1]; rw [h54160 x y y z w u]

@[equational_result]
theorem Equation54083_implies_Equation54160 (G : Type*) [Magma G] (h54083 : Equation54083 G) : Equation54160 G := by
  have l0 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [← h54083 (sK0 ◇ sK1) X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54083 X1 (sK0 ◇ sK1) X0 sK0 sK1]
  have l1 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [h54083 X0 (sK0 ◇ sK1) sK2 sK0 sK1]
  have l2 : ∀ sK3 sK4 sK0 sK1 sK2 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK0 sK1 sK2
    conv => enter [1]; rw [h54083 sK3 sK4 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK4 sK2 sK0 sK1]
  have l3 : ∀ sK3 sK4 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4 sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54083 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK3 sK4 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 X0 sK2 sK3 sK4 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK0 sK1 X0 sK2 sK3 sK4
    conv => enter [1]; rw [← h54083 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK3 sK4 sK0 sK1 sK2]
  have l5 : ∀ X0 sK2 sK0 sK1 sK3 sK4 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro X0 sK2 sK0 sK1 sK3 sK4
    conv => enter [1]; rw [← h54083 (sK0 ◇ sK1) X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK2 sK3 sK4]
  have l6 : ∀ sK3 sK4 X0 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X0 sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK3 sK4 sK2 sK0 sK1]
    conv => enter [1]; rw [← l5 X0 sK2 sK0 sK1 sK3 sK4]
  intro x y z w u v
  conv => enter [1]; rw [l6 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54091 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54091 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54160 sK1 sK2 sK1 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h54160 X0 X1 sK1 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [h54160 sK1 sK1 X2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54091_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54091 : Equation54091 G) : Equation54160 G := by
  have l0 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK4 ◇ ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [← h4512 sK4 sK3 ((sK4 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 (sK4 ◇ sK3) X0]
  have l1 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK4 ◇ ((sK3 ◇ X0) ◇ X1)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK4 sK3 X0]
    conv => enter [1]; rw [← h4512 sK4 (sK3 ◇ X0) X1]
  have l2 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK4 ◇ (sK3 ◇ (X0 ◇ X1))) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [l1 sK4 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK3 X0 X1]
  have l3 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [l2 sK4 sK3 X0 X1]
    conv => enter [1]; rw [← h54091 sK3 X0 sK4 X1]
  have l4 : ∀ sK4 sK3 X0 X1 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK4 ◇ sK3) X0 X1]
    conv => enter [1]; rw [l3 sK4 sK3 X0 X1]
  have l5 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4
    conv => enter [1]; rw [← l4 sK4 sK3 sK4 (sK3 ◇ (sK4 ◇ sK3))]
    conv => enter [1, 2]; rw [h4512 sK4 sK3 (sK4 ◇ sK3)]
  have l6 : ∀ sK3 sK4 X0 : G, (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) = ((sK4 ◇ sK3) ◇ (sK3 ◇ (X0 ◇ sK3))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← l4 sK4 sK3 (sK4 ◇ sK3) (X0 ◇ sK3)]
    conv => enter [1, 2]; rw [l4 sK4 sK3 X0 sK3]
  have l7 : ∀ sK3 sK4 : G, (sK3 ◇ (sK3 ◇ sK3)) = (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) := by
    intro sK3 sK4
    conv => enter [1]; rw [← l4 sK4 sK3 sK3 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l6 sK3 sK4 sK3]
  have l8 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l5 sK3 sK4]
    conv => enter [1]; rw [l4 sK4 sK3 (sK4 ◇ sK3) (sK4 ◇ sK3)]
  have l9 : ∀ sK3 sK4 : G, (sK3 ◇ (sK3 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK4
    conv => enter [1]; rw [l7 sK3 sK4]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) sK3]
  have l10 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK4
    conv => enter [1]; rw [l8 sK3 sK4]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) sK3]
  have l11 : ∀ sK4 sK3 : G, ((sK4 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ sK3))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) := by
    intro sK4 sK3
    conv => enter [1]; rw [l4 sK4 sK3 sK3 (sK4 ◇ sK3)]
    conv => enter [1]; rw [l9 sK3 sK4]
  have l12 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1, 1]; rw [← l4 sK4 sK3 sK4 sK3]
    conv => enter [1]; rw [← h4512 (sK4 ◇ sK3) (sK4 ◇ sK3) X0]
  have l13 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l12 sK3 sK4 X0]
    conv => enter [1]; rw [l4 sK4 sK3 (sK4 ◇ sK3) X0]
  have l14 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l13 sK3 sK4 X0]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) sK3]
  have l15 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = ((sK4 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l14 sK3 sK4 X0]
    conv => enter [1]; rw [← l11 sK4 sK3]
  have l16 : ∀ sK4 sK3 : G, ((sK4 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ sK3))) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK4 sK3
    conv => enter [1, 2]; rw [l10 sK3 sK4]
    conv => enter [1]; rw [l4 sK4 sK3 (sK3 ◇ (sK4 ◇ sK3)) sK3]
    conv => enter [1, 2]; rw [← l10 sK3 sK4]
  have l17 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK4 ◇ ((sK4 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ sK3)))) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l0 sK4 sK3 X0]
    conv => enter [1, 2]; rw [l15 sK3 sK4 X0]
  have l18 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK4 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3)))) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l17 sK4 sK3 X0]
    conv => enter [1, 2]; rw [l16 sK4 sK3]
  have l19 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = ((sK4 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l18 sK4 sK3 X0]
    conv => enter [1]; rw [h4512 sK4 sK3 (sK3 ◇ (sK4 ◇ sK3))]
  have l20 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l19 sK4 sK3 X0]
    conv => enter [1]; rw [l16 sK4 sK3]
  have l21 : ∀ sK3 sK4 : G, (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4
    conv => enter [1]; rw [← l4 sK4 sK3 (sK4 ◇ sK3) sK3]
    conv => enter [1]; rw [l20 sK4 sK3 sK3]
  have l22 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK3) sK3]
    conv => enter [1]; rw [l21 sK3 sK4]
  have l23 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4
    conv => enter [1]; rw [l10 sK3 sK4]
    conv => enter [1]; rw [l22 sK3 sK4]
  have l24 : ∀ sK4 sK3 X0 X1 : G, ((sK4 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ sK3))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [← l15 sK3 sK4 (X0 ◇ (X1 ◇ sK4))]
    conv => enter [1]; rw [← h54091 X0 X1 (sK3 ◇ (sK4 ◇ sK3)) sK4]
  have l25 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK4 ◇ sK3))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [← l16 sK4 sK3]
    conv => enter [1]; rw [l24 sK4 sK3 X0 X1]
  have l26 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l23 sK3 sK4]
    conv => enter [1]; rw [l25 sK3 sK4 X0 X1]
  have l27 : ∀ sK3 sK4 X2 X0 X1 X3 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro sK3 sK4 X2 X0 X1 X3
    conv => enter [1]; rw [l26 sK3 sK4 X0 X1]
    conv => enter [1]; rw [h54091 X0 X1 X2 X3]
  intro x y z w u v
  conv => enter [1]; rw [l27 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54097 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54097 G := by
  intro x y z w
  conv => enter [1]; rw [h54160 x y z x w y]

theorem Equation4512_54097_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54097 : Equation54097 G) : Equation54160 G := by
  have l0 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK4 ◇ ((sK3 ◇ X0) ◇ X1)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK4 sK3 X0]
    conv => enter [1]; rw [← h4512 sK4 (sK3 ◇ X0) X1]
  have l1 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK4 ◇ (sK3 ◇ (X0 ◇ X1))) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [l0 sK4 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK3 X0 X1]
  have l2 : ∀ sK4 sK3 X0 X1 : G, (((sK4 ◇ sK3) ◇ X0) ◇ X1) = (sK3 ◇ (X1 ◇ sK3)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [l1 sK4 sK3 X0 X1]
    conv => enter [1]; rw [← h54097 sK3 X1 sK4 X0]
  have l3 : ∀ sK4 sK3 X0 X1 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) = (sK3 ◇ (X1 ◇ sK3)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK4 ◇ sK3) X0 X1]
    conv => enter [1]; rw [l2 sK4 sK3 X0 X1]
  have l4 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK3 ◇ ((sK3 ◇ X0) ◇ sK3)) := by
    intro sK4 sK3 X0
    conv => enter [1, 2]; rw [← h4512 sK4 sK3 X0]
    conv => enter [1]; rw [l3 sK4 sK3 sK4 (sK3 ◇ X0)]
  have l5 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK3 ◇ (sK3 ◇ (X0 ◇ sK3))) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l4 sK4 sK3 X0]
    conv => enter [1, 2]; rw [← h4512 sK3 X0 sK3]
  have l6 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l5 sK4 sK3 X0]
    conv => enter [1]; rw [← h54097 sK3 sK3 sK3 X0]
  have l7 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l3 sK4 sK3 sK4 sK3]
    conv => enter [1]; rw [← l6 sK4 sK3 X0]
  have l8 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l7 sK4 sK3 X0]
    conv => enter [1]; rw [l3 sK4 sK3 (sK4 ◇ sK3) X0]
  have l9 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1, 1]; rw [← l8 sK4 sK3 sK4]
    conv => enter [1]; rw [← h4512 (sK4 ◇ sK3) (sK4 ◇ sK3) X0]
  have l10 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l9 sK3 sK4 X0]
    conv => enter [1]; rw [l3 sK4 sK3 (sK4 ◇ sK3) X0]
  have l11 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) = ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l10 sK3 sK4 X0]
    conv => enter [1]; rw [← l8 sK4 sK3 X0]
  have l12 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [← l8 sK4 sK3 sK4]
    conv => enter [1]; rw [← l11 sK3 sK4 X0]
  have l13 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l12 sK3 sK4 (X0 ◇ (sK3 ◇ X1))]
    conv => enter [1]; rw [← h54097 X0 X1 (sK3 ◇ (sK4 ◇ sK3)) sK3]
  have l14 : ∀ sK3 sK4 X1 X0 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X1 X0 sK0 sK1
    conv => enter [1]; rw [l13 sK3 sK4 X0 sK1]
    conv => enter [1]; rw [h54097 X0 sK1 X1 sK0]
  intro x y z w u v
  conv => enter [1]; rw [l14 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54100 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54100 G := by
  intro x y z w u
  conv => enter [1]; rw [h54160 x y z x w u]

theorem Equation4512_54100_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54100 : Equation54100 G) : Equation54160 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h54100 sK2 (sK0 ◇ sK1) X0 sK0 sK1]
  have l1 : ∀ X1 sK2 sK0 sK1 X0 : G, (X1 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h54100 sK2 (sK2 ◇ (sK0 ◇ sK1)) X1 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK1 X0]
  have l2 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 sK5]
    conv => enter [1]; rw [l2 sK2 sK0 sK1 X0 X1]
  have l4 : ∀ sK5 sK2 sK0 sK1 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l3 sK5 sK2 sK0 sK1 sK2 sK5]
    conv => enter [1]; rw [← l1 X1 sK2 sK0 sK1 sK5]
  have l5 : ∀ sK5 sK2 sK0 sK1 X1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK5 sK2 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l4 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK0 ◇ sK1)) X1]
  have l6 : ∀ sK3 sK4 X0 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X0 sK0 sK1
    conv => enter [1]; rw [h54100 sK3 sK4 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [h54100 (sK0 ◇ sK1) sK3 X0 sK0 sK1]
  have l7 : ∀ sK5 sK2 sK0 sK1 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l3 sK5 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h54100 (sK2 ◇ (sK0 ◇ sK1)) sK5 X1 sK0 sK1]
  have l8 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK5 sK2 sK0 sK1 sK5]
    conv => enter [1]; rw [← l5 sK5 sK2 sK0 sK1 (sK0 ◇ sK1) sK5]
  have l9 : ∀ X0 sK0 sK1 sK5 sK2 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK5 sK2
    conv => enter [1]; rw [← h54100 (sK0 ◇ sK1) (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK5 sK2 sK0 sK1]
  have l10 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l3 sK5 sK2 sK0 sK1 (sK0 ◇ sK1) sK5]
    conv => enter [1]; rw [← l9 X0 sK0 sK1 sK5 sK2]
  have l11 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK3 sK4 sK3 sK0 sK1]
    conv => enter [1]; rw [← l10 sK5 sK2 sK0 sK1 sK3]
  intro x y z w u v
  conv => enter [1]; rw [l11 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54104 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54104 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54160 sK1 sK2 sK1 sK1 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← h54160 X0 X1 sK1 sK1 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK1 sK2 X2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 X2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [h54160 sK1 sK1 X2 sK2 sK1 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_54104_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54104 : Equation54104 G) : Equation54160 G := by
  have l0 : ∀ sK3 sK4 X1 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X1 ◇ ((sK4 ◇ sK3) ◇ X0)) := by
    intro sK3 sK4 X1 X0
    conv => enter [1]; rw [h54104 sK3 sK4 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK4 sK3 X0]
  have l1 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l0 sK3 sK4 sK3 X0]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) X0]
  have l2 : ∀ sK3 sK4 X0 X1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [l1 sK3 sK4 (X1 ◇ (X0 ◇ sK3))]
    conv => enter [1]; rw [← h54104 X0 X1 (sK3 ◇ (sK4 ◇ sK3)) sK3]
  have l3 : ∀ sK3 sK4 X0 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 X0 sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK4 sK0 sK2]
    conv => enter [1]; rw [h54104 sK0 sK2 X0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [l3 x y z w u v]

@[equational_result]
theorem Equation54160_implies_Equation54117 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54117 G := by
  intro x y z w u
  conv => enter [1]; rw [h54160 x y z y w u]

theorem Equation4512_54117_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54117 : Equation54117 G) : Equation54160 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h54117 sK2 (sK0 ◇ sK1) X0 sK0 sK1]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54117 X0 (sK0 ◇ sK1) sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l2 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h54117 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X1 sK0 sK1]
    conv => enter [1, 2]; rw [h54117 (sK0 ◇ sK1) sK2 X0 sK0 sK1]
  have l3 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1, 2]; rw [h54117 (sK0 ◇ sK1) sK2 X0 sK0 sK1]
    conv => enter [1]; rw [h54117 (sK2 ◇ (sK0 ◇ sK1)) X0 X1 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h54117 (sK0 ◇ sK1) sK2 (X0 ◇ X1) sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h54117 (sK0 ◇ sK1) sK2 sK5 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0 X1]
  have l6 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [← l1 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X1 X0]
  have l7 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1 sK2 X0]
  have l8 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK5 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [← l7 sK2 sK0 sK1 sK5]
  have l9 : ∀ sK2 sK0 sK1 sK5 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 sK5
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h54117 (sK0 ◇ sK1) sK2 sK5 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 sK5 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 sK5
    conv => enter [1]; rw [h54117 (sK0 ◇ sK1) sK2 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [l9 sK2 sK0 sK1 sK5]
  have l11 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h54117 (sK0 ◇ sK1) sK2 sK5 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 sK2 sK5]
  have l12 : ∀ X0 sK2 sK0 sK1 sK5 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1 sK5
    conv => enter [1]; rw [← h54117 sK2 (sK2 ◇ (sK0 ◇ sK1)) X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK5 sK2 sK0 sK1]
  have l13 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l11 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← l12 X0 sK2 sK0 sK1 sK5]
  have l14 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK5 sK2 sK0 sK1 sK5]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1 sK5 (sK2 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ X1 X0 sK0 sK1 sK4 sK3 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro X1 X0 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← h54117 (sK4 ◇ (sK0 ◇ sK1)) X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h54117 sK3 sK4 X0 sK0 sK1]
  have l16 : ∀ sK3 sK4 X0 X1 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 X0 X1 sK0 sK1
    conv => enter [1]; rw [h54117 sK3 sK4 (X0 ◇ X1) sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK4 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK4 sK3 sK0 sK1 : G, (sK4 ◇ (sK3 ◇ (sK4 ◇ sK3))) = ((sK4 ◇ sK3) ◇ (sK4 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK3 sK0 sK1
    conv => enter [1, 2]; rw [h54117 sK3 sK4 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK4 sK3 (sK4 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK4 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4
    conv => enter [1]; rw [h54117 sK3 sK4 (sK4 ◇ sK3) sK3 sK3]
    conv => enter [1]; rw [← l17 sK4 sK3 sK3 sK3]
  have l19 : ∀ sK3 sK4 X0 : G, (sK3 ◇ (sK4 ◇ sK3)) = (X0 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l16 sK3 sK4 X0 sK3 sK3 sK3]
    conv => enter [1, 2]; rw [← h54117 sK3 sK4 sK3 sK3 sK3]
  have l20 : ∀ X1 X0 sK0 sK1 sK4 sK3 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK4 ◇ ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK4 ◇ sK3)))) := by
    intro X1 X0 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l15 X1 X0 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [← h4512 sK4 (sK0 ◇ sK1) (sK3 ◇ (sK4 ◇ sK3))]
  have l21 : ∀ sK4 sK3 X1 X0 sK0 sK1 : G, (sK4 ◇ (sK3 ◇ (sK4 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK3 X1 X0 sK0 sK1
    conv => enter [1, 2]; rw [l19 sK3 sK4 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l20 X1 X0 sK0 sK1 sK4 sK3]
  have l22 : ∀ sK4 sK3 sK2 sK0 sK1 : G, (sK4 ◇ (sK3 ◇ (sK4 ◇ sK3))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK4 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l21 sK4 sK3 sK4 sK4 sK0 sK1]
    conv => enter [1]; rw [← l6 sK2 sK0 sK1 sK4 sK4]
  have l23 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK4 ◇ (sK3 ◇ (sK4 ◇ sK3))) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l14 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← l22 sK4 sK3 sK2 sK0 sK1]
  have l24 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l18 sK3 sK4]
    conv => enter [1]; rw [← l23 sK5 sK2 sK0 sK1 sK4 sK3]
  intro x y z w u v
  conv => enter [1]; rw [l24 x y z w u v]

theorem Equation4512_54160_implies_Equation54136 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54160 : Equation54160 G) : Equation54136 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X0]
  have l1 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [h54160 sK1 sK2 X0 X1 sK0 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h54160 (sK1 ◇ sK2) sK1 X0 X1 sK0 (sK1 ◇ sK2)]
  have l3 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 sK2 sK1 sK1 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h54160 (sK1 ◇ sK2) sK1 X0 X1 sK1 sK2]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation4512_54136_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54136 : Equation54136 G) : Equation54160 G := by
  have l0 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ X0)) = (sK4 ◇ ((sK3 ◇ (sK4 ◇ sK3)) ◇ X0)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [← h4512 sK4 sK3 ((sK4 ◇ sK3) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 (sK4 ◇ sK3) X0]
  have l1 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X4 ◇ (X5 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [← h54136 X2 X3 X0 X1]
    conv => enter [1]; rw [h54136 X2 X3 X4 X5]
  have l2 : ∀ sK4 sK3 X0 X1 X2 : G, (sK4 ◇ ((sK3 ◇ X0) ◇ sK4)) = (X1 ◇ (X2 ◇ ((sK4 ◇ sK3) ◇ X0))) := by
    intro sK4 sK3 X0 X1 X2
    conv => enter [1]; rw [h54136 sK4 (sK3 ◇ X0) X1 X2]
    conv => enter [1, 2, 2]; rw [h4512 sK4 sK3 X0]
  have l3 : ∀ sK4 sK3 X0 X1 : G, (sK4 ◇ ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK4)) = (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)))) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [h54136 sK4 (sK3 ◇ (sK4 ◇ sK3)) X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK4 sK3 (sK4 ◇ sK3)]
  have l4 : ∀ sK0 sK1 X0 X1 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) = (X1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [h54136 (sK0 ◇ sK1) X0 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK3 X0 X1 sK4 : G, (sK3 ◇ (X0 ◇ sK3)) = (X1 ◇ ((sK4 ◇ sK3) ◇ X0)) := by
    intro sK3 X0 X1 sK4
    conv => enter [1]; rw [h54136 sK3 X0 X1 sK4]
    conv => enter [1, 2]; rw [h4512 sK4 sK3 X0]
  have l6 : ∀ sK2 sK0 sK1 X0 X1 sK5 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X1 ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0 X1 sK5
    conv => enter [1]; rw [h54136 (sK2 ◇ (sK0 ◇ sK1)) X0 X1 sK5]
    conv => enter [1, 2]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l7 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54136 X0 X1 sK2 (sK0 ◇ sK1)]
  have l8 : ∀ sK3 sK4 X0 X1 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK4 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK3) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54136 X0 X1 sK3 (sK4 ◇ sK3)]
  have l9 : ∀ sK4 sK3 X0 X1 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK4 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54136 X0 X1 sK4 sK3]
  have l10 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54136 X0 X1 sK5 (sK2 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ X1 sK5 sK2 sK0 sK1 X0 sK4 sK3 : G, (X1 ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK4 ◇ sK3) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 sK5 sK2 sK0 sK1 X0 sK4 sK3
    conv => enter [1]; rw [← l6 sK2 sK0 sK1 X0 X1 sK5]
    conv => enter [1]; rw [← l9 sK4 sK3 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l12 : ∀ X1 sK2 sK0 sK1 X0 sK4 sK3 : G, (X1 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X1 sK2 sK0 sK1 X0 sK4 sK3
    conv => enter [1]; rw [← l4 sK0 sK1 X0 X1 sK2]
    conv => enter [1]; rw [← l9 sK4 sK3 (sK0 ◇ sK1) X0]
  have l13 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) = (X0 ◇ (X1 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [h54136 sK5 (sK2 ◇ (sK0 ◇ sK1)) X0 X1]
  have l14 : ∀ sK4 sK3 : G, (sK4 ◇ ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK4)) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3))) := by
    intro sK4 sK3
    conv => enter [1]; rw [l3 sK4 sK3 sK4 sK4]
    conv => enter [1]; rw [← h54136 (sK4 ◇ sK3) (sK4 ◇ sK3) sK4 sK4]
  have l15 : ∀ sK4 sK3 X0 : G, (sK4 ◇ ((sK3 ◇ X0) ◇ sK4)) = ((sK4 ◇ sK3) ◇ (X0 ◇ (sK4 ◇ sK3))) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l2 sK4 sK3 X0 sK4 sK4]
    conv => enter [1]; rw [← h54136 (sK4 ◇ sK3) X0 sK4 sK4]
  have l16 : ∀ sK4 sK3 X0 X1 : G, ((sK4 ◇ sK3) ◇ sK4) = (X0 ◇ (X1 ◇ (sK4 ◇ sK3))) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK4 sK3 sK4]
    conv => enter [1]; rw [h54136 sK4 sK3 X0 X1]
  have l17 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h54136 sK2 (sK0 ◇ sK1) X0 X1]
  have l18 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h54136 sK0 sK1 X0 X1]
  have l19 : ∀ sK3 sK4 : G, (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) = (sK4 ◇ ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l5 sK3 (sK4 ◇ sK3) (sK4 ◇ sK3) sK4]
    conv => enter [1]; rw [← l14 sK4 sK3]
  have l20 : ∀ sK4 sK3 X0 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ (sK4 ◇ sK3))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK4 ◇ (sK3 ◇ X0))) := by
    intro sK4 sK3 X0 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← l15 sK4 sK3 X0]
    conv => enter [1]; rw [← l10 sK5 sK2 sK0 sK1 sK4 (sK3 ◇ X0)]
  have l21 : ∀ sK3 sK4 : G, (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ sK4)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l19 sK3 sK4]
    conv => enter [1]; rw [← l0 sK4 sK3 sK4]
  have l22 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ (sK4 ◇ sK3))) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l20 sK4 sK3 X0 sK4 sK4 sK4 sK4]
    conv => enter [1]; rw [← h54136 sK3 X0 (sK4 ◇ (sK4 ◇ (sK4 ◇ sK4))) sK4]
  have l23 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = (sK3 ◇ ((sK4 ◇ sK3) ◇ sK3)) := by
    intro sK3 sK4
    conv => enter [1]; rw [l5 sK3 sK4 (sK4 ◇ sK3) sK4]
    conv => enter [1]; rw [← l21 sK3 sK4]
  have l24 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ sK4) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l16 sK4 sK3 (sK4 ◇ sK3) X0]
    conv => enter [1]; rw [l22 sK4 sK3 X0]
  have l25 : ∀ sK3 sK4 : G, (sK3 ◇ (sK4 ◇ sK3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) := by
    intro sK3 sK4
    conv => enter [1]; rw [l23 sK3 sK4]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) sK3]
  have l26 : ∀ sK3 sK4 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ sK3) = ((sK4 ◇ sK3) ◇ sK4) := by
    intro sK3 sK4
    conv => enter [1]; rw [← l25 sK3 sK4]
    conv => enter [1]; rw [← l24 sK4 sK3 sK4]
  have l27 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK3 ◇ X0)) = (((sK4 ◇ sK3) ◇ sK4) ◇ X0) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK4 ◇ sK3)) sK3 X0]
    conv => enter [1, 1]; rw [l26 sK3 sK4]
  have l28 : ∀ sK3 sK4 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK3 ◇ X0)) = ((sK4 ◇ sK3) ◇ (sK4 ◇ X0)) := by
    intro sK3 sK4 X0
    conv => enter [1]; rw [l27 sK3 sK4 X0]
    conv => enter [1]; rw [← h4512 (sK4 ◇ sK3) sK4 X0]
  have l29 : ∀ sK3 X0 sK4 : G, (sK3 ◇ (X0 ◇ sK3)) = ((sK4 ◇ sK3) ◇ (sK4 ◇ X0)) := by
    intro sK3 X0 sK4
    conv => enter [1]; rw [← l8 sK3 sK4 sK3 X0]
    conv => enter [1]; rw [l28 sK3 sK4 X0]
  have l30 : ∀ sK4 sK3 X0 : G, ((sK4 ◇ sK3) ◇ sK4) = ((sK4 ◇ sK3) ◇ (sK4 ◇ X0)) := by
    intro sK4 sK3 X0
    conv => enter [1]; rw [l24 sK4 sK3 X0]
    conv => enter [1]; rw [l29 sK3 X0 sK4]
  have l31 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) = ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l13 sK5 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [h4512 sK4 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l32 : ∀ sK5 sK2 sK0 sK1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK5 sK2 sK0 sK1 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l33 : ∀ sK2 sK0 sK1 X0 sK5 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = (sK2 ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5)) := by
    intro sK2 sK0 sK1 X0 sK5
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l13 sK5 sK2 sK0 sK1 (sK0 ◇ sK1) X0]
  have l34 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = (sK5 ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l13 sK5 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l35 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l34 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK5 sK2 sK0 sK1 sK5 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l36 : ∀ sK2 sK0 sK1 X0 sK5 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK4 ◇ sK3) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK5)) := by
    intro sK2 sK0 sK1 X0 sK5 sK4 sK3
    conv => enter [1]; rw [l33 sK2 sK0 sK1 X0 sK5]
    conv => enter [1]; rw [l11 sK2 sK5 sK2 sK0 sK1 sK5 sK4 sK3]
  have l37 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l35 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK5 sK2 sK0 sK1 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK5]
  have l38 : ∀ sK2 sK0 sK1 X0 sK5 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ sK5)) := by
    intro sK2 sK0 sK1 X0 sK5 sK4 sK3
    conv => enter [1]; rw [l36 sK2 sK0 sK1 X0 sK5 sK4 sK3]
    conv => enter [1]; rw [l12 (sK4 ◇ sK3) sK2 sK0 sK1 sK5 sK4 sK3]
  have l39 : ∀ sK5 sK2 sK0 sK1 X0 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK4 ◇ sK3) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 X0 sK4 sK3
    conv => enter [1]; rw [l37 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l11 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK5 sK2 sK0 sK1 sK5 sK4 sK3]
  have l40 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l13 sK5 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [l38 sK2 sK0 sK1 sK5 sK5 sK4 sK3]
  have l41 : ∀ sK5 sK2 sK0 sK1 X0 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 X0 sK4 sK3
    conv => enter [1]; rw [l39 sK5 sK2 sK0 sK1 X0 sK4 sK3]
    conv => enter [1]; rw [l12 (sK4 ◇ sK3) sK2 sK0 sK1 sK5 sK4 sK3]
  have l42 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l32 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l40 sK5 sK2 sK0 sK1 sK4 sK3]
  have l43 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 X0 : G, ((sK4 ◇ sK3) ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ sK5)) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l9 sK4 sK3 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l41 sK5 sK2 sK0 sK1 X0 sK4 sK3]
  have l44 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 X0 : G, ((sK4 ◇ sK3) ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l43 sK4 sK3 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l42 sK5 sK2 sK0 sK1 sK4 sK3]
  have l45 : ∀ sK4 sK3 sK2 sK0 sK1 X0 sK5 : G, ((sK4 ◇ sK3) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK3 sK2 sK0 sK1 X0 sK5
    conv => enter [1]; rw [← l11 (sK4 ◇ sK3) sK5 sK2 sK0 sK1 X0 sK4 sK3]
    conv => enter [1]; rw [l44 sK4 sK3 sK5 sK2 sK0 sK1 X0]
  have l46 : ∀ sK4 sK3 sK0 sK1 X0 sK5 sK2 : G, ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK3 sK0 sK1 X0 sK5 sK2
    conv => enter [1]; rw [← l12 (sK4 ◇ sK3) sK2 sK0 sK1 X0 sK4 sK3]
    conv => enter [1]; rw [l45 sK4 sK3 sK2 sK0 sK1 X0 sK5]
  have l47 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← l31 sK5 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [l32 sK5 sK2 sK0 sK1]
  have l48 : ∀ sK4 sK3 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ sK4) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK4 ◇ sK3)) := by
    intro sK4 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK4 sK3 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK4 ◇ sK3)]
  have l49 : ∀ sK4 sK3 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK4 ◇ sK3) ◇ sK4) := by
    intro sK4 sK3
    conv => enter [1]; rw [← h4512 sK4 sK3 (sK4 ◇ sK3)]
    conv => enter [1]; rw [← l16 sK4 sK3 sK4 sK3]
  have l50 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ sK4) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK4 ◇ sK3)) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK4 sK3 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK4 ◇ sK3)]
  have l51 : ∀ sK4 sK3 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK4 ◇ sK3)) := by
    intro sK4 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l49 sK4 sK3]
    conv => enter [1]; rw [l48 sK4 sK3 sK2 sK0 sK1]
  have l52 : ∀ X0 X1 sK4 sK3 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ sK4))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l50 sK4 sK3 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54136 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK4 ◇ sK3) X0 X1]
  have l53 : ∀ X0 X1 sK4 sK3 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ sK4))) = ((sK4 ◇ sK3) ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK4 ◇ sK3))) := by
    intro X0 X1 sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l52 X0 X1 sK4 sK3 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l10 sK5 sK2 sK0 sK1 (sK4 ◇ sK3) (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l54 : ∀ X0 X1 sK4 sK3 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ sK4))) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l53 X0 X1 sK4 sK3 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← l9 sK4 sK3 (sK4 ◇ sK3) (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l55 : ∀ sK5 sK2 sK0 sK1 X0 X1 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) = (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ sK4))) := by
    intro sK5 sK2 sK0 sK1 X0 X1 sK4 sK3
    conv => enter [1]; rw [l13 sK5 sK2 sK0 sK1 (sK4 ◇ sK3) (sK4 ◇ sK3)]
    conv => enter [1]; rw [← l54 X0 X1 sK4 sK3 sK5 sK2 sK0 sK1]
  have l56 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) = ((sK4 ◇ sK3) ◇ (sK4 ◇ (sK4 ◇ sK3))) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l55 sK5 sK2 sK0 sK1 sK5 sK5 sK4 sK3]
    conv => enter [1]; rw [← h54136 (sK4 ◇ sK3) sK4 sK5 sK5]
  have l57 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ sK4) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK5) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l30 sK4 sK3 (sK4 ◇ sK3)]
    conv => enter [1]; rw [← l56 sK5 sK2 sK0 sK1 sK4 sK3]
  have l58 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ sK4) = ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l57 sK4 sK3 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l31 sK5 sK2 sK0 sK1 sK4 sK3]
  have l59 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l49 sK4 sK3]
    conv => enter [1]; rw [l58 sK4 sK3 sK5 sK2 sK0 sK1]
  have l60 : ∀ X0 X1 sK4 sK3 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK4 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK4 sK3 sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l51 sK4 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [← h54136 (sK2 ◇ (sK0 ◇ sK1)) (sK4 ◇ sK3) X0 X1]
  have l61 : ∀ X0 X1 sK4 sK3 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)))) = ((sK4 ◇ sK3) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK4 ◇ sK3))) := by
    intro X0 X1 sK4 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l60 X0 X1 sK4 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [l7 sK2 sK0 sK1 (sK4 ◇ sK3) (sK2 ◇ (sK0 ◇ sK1))]
  have l62 : ∀ X0 X1 sK4 sK3 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)))) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK4 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l61 X0 X1 sK4 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [← l9 sK4 sK3 (sK4 ◇ sK3) (sK2 ◇ (sK0 ◇ sK1))]
  have l63 : ∀ sK2 sK0 sK1 X0 X1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = (X0 ◇ (X1 ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)))) := by
    intro sK2 sK0 sK1 X0 X1 sK4 sK3
    conv => enter [1]; rw [l17 sK2 sK0 sK1 (sK4 ◇ sK3) (sK4 ◇ sK3)]
    conv => enter [1]; rw [← l62 X0 X1 sK4 sK3 sK2 sK0 sK1]
  have l64 : ∀ sK2 sK0 sK1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = ((sK4 ◇ sK3) ◇ ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3))) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l63 sK2 sK0 sK1 sK2 sK2 sK4 sK3]
    conv => enter [1]; rw [← h54136 (sK4 ◇ sK3) (sK4 ◇ sK3) sK2 sK2]
  have l65 : ∀ sK2 sK0 sK1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = ((sK4 ◇ sK3) ◇ sK4) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l64 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [← l16 sK4 sK3 (sK4 ◇ sK3) (sK4 ◇ sK3)]
  have l66 : ∀ sK4 sK3 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) := by
    intro sK4 sK3 sK2 sK0 sK1
    conv => enter [1]; rw [l49 sK4 sK3]
    conv => enter [1]; rw [← l65 sK2 sK0 sK1 sK4 sK3]
  have l67 : ∀ sK2 sK0 sK1 sK5 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 sK5
    conv => enter [1]; rw [l17 sK2 sK0 sK1 sK5 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l68 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l66 sK4 sK3 sK2 sK0 sK1]
    conv => enter [1]; rw [l67 sK2 sK0 sK1 sK5]
  have l69 : ∀ X0 X1 sK0 sK1 X2 : G, (X0 ◇ ((X1 ◇ (sK0 ◇ sK1)) ◇ X2)) = (((sK0 ◇ sK1) ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 sK1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK0 ◇ sK1)) X2]
    conv => enter [1, 1]; rw [← l18 sK0 sK1 X0 X1]
  have l70 : ∀ sK0 sK1 sK4 sK3 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l18 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [h4512 sK4 sK3 (sK0 ◇ sK1)]
  have l71 : ∀ X0 X1 sK0 sK1 X2 : G, (X0 ◇ ((X1 ◇ (sK0 ◇ sK1)) ◇ X2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro X0 X1 sK0 sK1 X2
    conv => enter [1]; rw [l69 X0 X1 sK0 sK1 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X2]
  have l72 : ∀ X0 X1 sK0 sK1 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro X0 X1 sK0 sK1 X2
    conv => enter [1, 2]; rw [h4512 X1 (sK0 ◇ sK1) X2]
    conv => enter [1]; rw [l71 X0 X1 sK0 sK1 X2]
  have l73 : ∀ sK0 sK1 X2 : G, ((sK0 ◇ sK1) ◇ (X2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [h54136 (sK0 ◇ sK1) X2 sK0 sK0]
    conv => enter [1]; rw [l72 sK0 sK0 sK0 sK1 X2]
  have l74 : ∀ sK4 sK3 sK0 sK1 X2 : G, ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ X2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro sK4 sK3 sK0 sK1 X2
    conv => enter [1]; rw [l9 sK4 sK3 (sK0 ◇ sK1) X2]
    conv => enter [1]; rw [l73 sK0 sK1 X2]
  have l75 : ∀ sK5 sK2 sK0 sK1 X2 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro sK5 sK2 sK0 sK1 X2
    conv => enter [1]; rw [← l46 sK5 sK5 sK0 sK1 X2 sK5 sK2]
    conv => enter [1]; rw [l74 sK5 sK5 sK0 sK1 X2]
  have l76 : ∀ sK4 sK3 sK5 sK2 sK0 sK1 X2 : G, ((sK4 ◇ sK3) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro sK4 sK3 sK5 sK2 sK0 sK1 X2
    conv => enter [1]; rw [l47 sK4 sK3 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l75 sK5 sK2 sK0 sK1 X2]
  have l77 : ∀ sK4 sK3 sK0 sK1 X2 : G, ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X2)) := by
    intro sK4 sK3 sK0 sK1 X2
    conv => enter [1]; rw [l59 sK4 sK3 sK4 sK4 sK0 sK1]
    conv => enter [1]; rw [l76 sK4 sK3 sK4 sK4 sK0 sK1 X2]
  have l78 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l18 sK0 sK1 sK5 sK2]
    conv => enter [1]; rw [l18 sK0 sK1 X0 sK2]
  have l79 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [← l18 sK0 sK1 sK5 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l80 : ∀ sK5 sK2 sK0 sK1 X0 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) := by
    intro sK5 sK2 sK0 sK1 X0 sK4 sK3
    conv => enter [1]; rw [l79 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l77 sK4 sK3 sK0 sK1 X0]
  have l81 : ∀ sK3 sK5 sK2 sK0 sK1 sK4 : G, (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK5 sK2 sK0 sK1 sK4
    conv => enter [1, 2]; rw [l78 sK5 sK2 sK0 sK1 (sK4 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) (sK2 ◇ (sK0 ◇ sK1))]
  have l82 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l78 sK5 sK2 sK0 sK1 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l68 sK4 sK3 sK5 sK2 sK0 sK1]
  have l83 : ∀ sK5 sK2 sK0 sK1 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 sK3
    conv => enter [1]; rw [l78 sK5 sK2 sK0 sK1 (sK3 ◇ (sK5 ◇ sK3))]
    conv => enter [1]; rw [← l81 sK3 sK5 sK2 sK0 sK1 sK5]
  have l84 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l18 sK0 sK1 sK5 sK2]
    conv => enter [1]; rw [l70 sK0 sK1 sK4 sK3]
  have l85 : ∀ sK3 sK5 sK2 sK0 sK1 sK4 : G, (sK3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK0 ◇ sK1)) := by
    intro sK3 sK5 sK2 sK0 sK1 sK4
    conv => enter [1, 2]; rw [l84 sK5 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) (sK0 ◇ sK1)]
  have l86 : ∀ sK5 sK2 sK0 sK1 sK3 sK4 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1 sK3 sK4
    conv => enter [1]; rw [l83 sK5 sK2 sK0 sK1 sK3]
    conv => enter [1]; rw [l85 sK3 sK5 sK2 sK0 sK1 sK4]
  have l87 : ∀ sK5 sK2 sK0 sK1 X0 X1 X2 X3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro sK5 sK2 sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [l1 sK5 (sK2 ◇ (sK0 ◇ sK1)) X0 X1 X2 X3]
  have l88 : ∀ X0 X1 X2 X3 sK3 sK4 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3 sK3 sK4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 sK3 (sK4 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) (X2 ◇ X3)]
  have l89 : ∀ X0 X1 X2 X3 sK4 sK3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = ((sK4 ◇ sK3) ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3 sK4 sK3
    conv => enter [1]; rw [l1 X0 X1 X2 X3 sK4 sK3]
    conv => enter [1]; rw [h4512 sK4 sK3 (X2 ◇ X3)]
  have l90 : ∀ sK4 sK3 X2 X3 : G, ((sK4 ◇ sK3) ◇ (X2 ◇ X3)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (X2 ◇ X3)) := by
    intro sK4 sK3 X2 X3
    conv => enter [1]; rw [← l89 sK4 sK4 X2 X3 sK4 sK3]
    conv => enter [1]; rw [l88 sK4 sK4 X2 X3 sK3 sK4]
  have l91 : ∀ sK4 sK3 X0 X1 sK5 sK2 sK0 sK1 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK4 sK3 X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← l89 sK4 sK4 X0 X1 sK4 sK3]
    conv => enter [1]; rw [← l87 sK5 sK2 sK0 sK1 X0 X1 sK4 sK4]
  have l92 : ∀ sK4 sK3 X0 X1 : G, ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) = ((sK4 ◇ sK3) ◇ (sK4 ◇ sK3)) := by
    intro sK4 sK3 X0 X1
    conv => enter [1]; rw [l91 sK4 sK3 X0 X1 sK4 sK4 sK4 sK4]
    conv => enter [1]; rw [l80 sK4 sK4 sK4 sK4 (X0 ◇ X1) sK4 sK3]
  have l93 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK3) ◇ (X0 ◇ X1)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3 X0 X1
    conv => enter [1]; rw [l82 sK5 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [← l92 sK4 sK3 X0 X1]
  have l94 : ∀ sK5 sK2 sK0 sK1 X0 sK3 sK4 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0 sK3 sK4
    conv => enter [1, 1]; rw [l86 sK5 sK2 sK0 sK1 sK3 sK4]
    conv => enter [1]; rw [← h4512 (sK3 ◇ (sK4 ◇ sK3)) (sK0 ◇ sK1) X0]
  have l95 : ∀ sK5 sK2 sK0 sK1 X0 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK4 ◇ sK3) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0 sK4 sK3
    conv => enter [1]; rw [l94 sK5 sK2 sK0 sK1 X0 sK3 sK4]
    conv => enter [1]; rw [← l90 sK4 sK3 (sK0 ◇ sK1) X0]
  have l96 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l93 sK5 sK2 sK0 sK1 sK5 sK5 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← l95 sK5 sK2 sK0 sK1 X0 sK5 sK5]
  have l97 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l96 sK5 sK2 sK0 sK1 (sK5 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h54136 X0 X1 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK5]
  intro x y z w u v
  conv => enter [1]; rw [← l97 z w u v x y]

@[equational_result]
theorem Equation54160_implies_Equation54139 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54139 G := by
  have l0 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h54160 sK2 sK3 sK2 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54160 X0 X1 sK2 sK2 sK2 (sK2 ◇ sK2)]
  have l1 : ∀ sK2 sK3 X2 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK3 X2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [h54160 sK2 sK2 X2 sK1 sK2 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]

theorem Equation4512_54139_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54139 : Equation54139 G) : Equation54160 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h54139 sK0 sK1 X0 X1 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54139 sK0 X0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h54139 sK0 X0 sK2 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 X0 sK4 sK3 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK4 sK3 sK1
    conv => enter [1]; rw [h54139 sK0 X0 sK4 sK3 sK1]
    conv => enter [1]; rw [h4512 sK4 sK3 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 X0 sK5 sK2 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK5 sK2 sK1
    conv => enter [1]; rw [h54139 sK0 X0 sK5 (sK2 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l5 : ∀ sK2 sK0 sK1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l2 sK0 sK2 sK2 sK1]
    conv => enter [1]; rw [l3 sK0 sK2 sK4 sK3 sK1]
  have l6 : ∀ sK0 sK1 sK4 sK3 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l1 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK0 sK4 sK3 sK1]
  have l7 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK5 ◇ ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1 sK4 sK3]
  have l8 : ∀ sK0 sK1 sK5 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK5 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK5 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK5 sK2 sK0 sK1 sK0 sK0]
  have l9 : ∀ sK2 sK0 sK1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK2 ◇ ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK4 sK3]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK2 sK0 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 sK4 sK3 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1 sK4 sK3]
  have l12 : ∀ X2 sK2 sK0 sK1 X0 : G, (X2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h54139 sK0 X2 X2 sK2 sK1]
    conv => enter [1]; rw [h54139 sK0 X2 X0 sK2 sK1]
  have l13 : ∀ sK0 X0 X1 X2 sK2 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 X1 X2 sK2 sK1
    conv => enter [1]; rw [h54139 sK0 X0 (X1 ◇ X2) sK2 sK1]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ (sK0 ◇ sK1))]
  have l14 : ∀ X1 X2 sK2 sK0 sK1 sK5 : G, (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK2 sK0 sK1 sK5
    conv => enter [1]; rw [← l13 sK0 X1 X1 X2 sK2 sK1]
    conv => enter [1]; rw [l4 sK0 X1 sK5 sK2 sK1]
  have l15 : ∀ sK0 sK1 X1 X2 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l14 X1 X2 sK2 sK0 sK1 sK0]
  have l16 : ∀ X1 X2 sK2 sK0 sK1 sK4 sK3 : G, (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l15 sK0 sK1 X1 X2 sK2]
    conv => enter [1]; rw [l11 sK0 sK1 sK4 sK3]
  have l17 : ∀ X1 X2 X3 X4 X0 sK2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X4 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X1 X2 X3 X4 X0 sK2 sK0 sK1
    conv => enter [1]; rw [h54139 X1 X2 X3 X4 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l12 X1 sK2 sK0 sK1 X0]
  have l18 : ∀ sK3 sK4 sK2 sK0 sK1 X0 : G, ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK4 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK3 (sK4 ◇ sK3) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l12 (sK4 ◇ sK3) sK2 sK0 sK1 X0]
  have l19 : ∀ sK4 sK3 sK0 sK1 sK2 : G, ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK3 sK4 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [← l18 sK3 sK4 sK2 sK0 sK1 sK4]
  have l20 : ∀ X1 X2 X3 sK4 sK3 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1))) := by
    intro X1 X2 X3 sK4 sK3 sK0 sK1
    conv => enter [1]; rw [l17 X1 X2 X3 X1 X1 X1 sK0 sK1]
    conv => enter [1, 2]; rw [l16 X1 X1 X1 sK0 sK1 sK4 sK3]
  have l21 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l12 sK5 sK2 sK0 sK1 (sK3 ◇ (sK4 ◇ sK3))]
    conv => enter [1]; rw [← l19 sK4 sK3 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 X1 X2 : G, ((sK0 ◇ sK1) ◇ sK0) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 X1 X2 sK0 sK0 sK0 sK0 sK1]
  have l23 : ∀ sK4 sK3 sK0 sK1 X1 X2 : G, ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK4 sK3 sK0 sK1 X1 X2
    conv => enter [1]; rw [← l11 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [l22 sK0 sK1 X1 X2]
  have l24 : ∀ sK5 sK2 sK0 sK1 X1 X2 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK5 sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l21 sK5 sK2 sK0 sK1 sK5 sK5]
    conv => enter [1]; rw [l23 sK5 sK5 sK0 sK1 X1 X2]
  intro x y z w u v
  conv => enter [1]; rw [← l24 z w u v x y]

@[equational_result]
theorem Equation54160_implies_Equation54144 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54144 G := by
  have l0 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [h54160 sK2 sK3 sK2 sK2 sK2 (sK3 ◇ sK2)]
    conv => enter [1]; rw [← h54160 X0 X1 sK2 sK2 sK2 (sK3 ◇ sK2)]
  have l1 : ∀ sK2 sK3 X2 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (X2 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 X2 sK1 sK0
    conv => enter [1]; rw [l0 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [h54160 sK2 sK2 X2 sK1 sK3 sK0]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]

@[equational_result]
theorem Equation54144_implies_Equation54160 (G : Type*) [Magma G] (h54144 : Equation54144 G) : Equation54160 G := by
  have l0 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h54144 sK1 sK0 sK5 sK2 sK1]
    conv => enter [1]; rw [h54144 sK1 sK0 X0 sK2 sK1]
  have l1 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h54144 sK1 sK0 sK5 sK2 sK1]
    conv => enter [1]; rw [h54144 sK1 sK0 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h54144 sK1 sK0 sK5 sK2 sK1]
  have l2 : ∀ X0 X1 X2 X3 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 X2 X3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [h54144 X0 X1 X2 X3 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l0 X1 sK2 sK0 sK1 sK5]
  have l3 : ∀ X0 X1 X2 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l2 X0 X1 X2 X0 sK5 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK5 sK2 sK0 sK1 X0]
  have l4 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK5 sK2 sK0 sK1 sK5]
    conv => enter [1]; rw [← l3 X0 X1 sK5 sK5 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [← l4 z w u v x y]

@[equational_result]
theorem Equation54160_implies_Equation54156 (G : Type*) [Magma G] (h54160 : Equation54160 G) : Equation54156 G := by
  intro x y z w u
  conv => enter [1]; rw [h54160 x y z w u y]

theorem Equation4512_54156_implies_Equation54160 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54156 : Equation54156 G) : Equation54160 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54156 X0 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h54156 X0 sK1 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l2 : ∀ X0 sK1 sK4 sK3 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK4 sK3 sK0
    conv => enter [1]; rw [h54156 X0 sK1 sK4 sK3 sK0]
    conv => enter [1]; rw [h4512 sK4 sK3 (sK0 ◇ sK1)]
  have l3 : ∀ X2 X3 X0 X1 sK0 sK1 : G, (X2 ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X2 X3 X0 X1 sK0 sK1
    conv => enter [1]; rw [h54156 X2 X3 (X2 ◇ X3) sK1 X2]
    conv => enter [1]; rw [h54156 (X2 ◇ X3) sK1 X0 X1 sK0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h54156 sK0 sK1 X0 X1 sK0]
  have l5 : ∀ X2 X3 sK0 sK1 : G, (X2 ◇ (X3 ◇ X2)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro X2 X3 sK0 sK1
    conv => enter [1]; rw [l3 X2 X3 X2 X2 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 X2 X2]
  have l6 : ∀ sK2 sK0 sK1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l1 sK2 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK2 sK1 sK4 sK3 sK0]
  have l7 : ∀ sK0 sK1 sK4 sK3 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 sK4 sK3 sK0]
  have l8 : ∀ sK2 sK0 sK1 sK4 sK3 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK2 ◇ ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK4 sK3]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 sK4 sK3 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 sK1 sK4 sK3]
  have l11 : ∀ X2 sK2 sK0 sK1 X0 : G, (X2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h54156 X2 sK1 X2 sK2 sK0]
    conv => enter [1]; rw [h54156 X2 sK1 X0 sK2 sK0]
  have l12 : ∀ X1 X2 sK2 sK0 sK1 X0 : G, (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK1 ◇ X0)) := by
    intro X1 X2 sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 X1 X2 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h54156 X0 sK1 (X1 ◇ X2) sK2 sK0]
  have l13 : ∀ sK0 sK1 X1 X2 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l12 X1 X2 sK2 sK0 sK1 sK0]
  have l14 : ∀ X1 X2 sK2 sK0 sK1 sK4 sK3 : G, (X1 ◇ (X2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [← l13 sK0 sK1 X1 X2 sK2]
    conv => enter [1]; rw [l10 sK0 sK1 sK4 sK3]
  have l15 : ∀ sK3 X0 sK2 sK0 sK1 sK4 : G, (sK3 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK3 X0 sK2 sK0 sK1 sK4
    conv => enter [1, 2]; rw [l11 X0 sK2 sK0 sK1 (sK4 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK3 (sK4 ◇ sK3) (sK2 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK4 sK3 sK0 sK1 sK2 : G, ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK4 ◇ sK3)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK4 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK3 sK4 sK2 sK0 sK1 sK4 sK3]
    conv => enter [1]; rw [l15 sK3 sK4 sK2 sK0 sK1 sK4]
  have l17 : ∀ sK5 sK2 sK0 sK1 sK4 sK3 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1 sK4 sK3
    conv => enter [1]; rw [l11 sK5 sK2 sK0 sK1 (sK3 ◇ (sK4 ◇ sK3))]
    conv => enter [1]; rw [← l16 sK4 sK3 sK0 sK1 sK2]
  have l18 : ∀ X2 X3 X0 X1 sK2 sK0 sK1 : G, (X2 ◇ (X3 ◇ X2)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X2 X3 X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [h54156 X2 X3 (X2 ◇ X3) (sK0 ◇ sK1) X2]
    conv => enter [1]; rw [h54156 (X2 ◇ X3) (sK0 ◇ sK1) X0 X1 sK2]
  have l19 : ∀ X2 X3 sK4 sK3 sK0 sK1 : G, (X2 ◇ (X3 ◇ X2)) = ((sK4 ◇ sK3) ◇ (sK0 ◇ sK1)) := by
    intro X2 X3 sK4 sK3 sK0 sK1
    conv => enter [1]; rw [l18 X2 X3 X2 X2 X2 sK0 sK1]
    conv => enter [1]; rw [l14 X2 X2 X2 sK0 sK1 sK4 sK3]
  have l20 : ∀ X2 X3 sK5 sK2 sK0 sK1 : G, (X2 ◇ (X3 ◇ X2)) = (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X2 X3 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l19 X2 X3 X2 X2 sK0 sK1]
    conv => enter [1]; rw [← l17 sK5 sK2 sK0 sK1 X2 X2]
  intro x y z w u v
  conv => enter [1]; rw [l20 x y z w u v]

theorem Equation4512_54067_implies_Equation54101 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54101 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l11 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l6 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l12 X1 X0 X2]
  have l14 : ∀ X0 X1 sK1 sK0 : G, ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ sK0) sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l5 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l22 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l14 X0 X1 sK1 sK0]
  have l23 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l22 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l10 sK0 X0 sK1]
    conv => enter [1]; rw [l23 sK0 X0 X1 sK1]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54067 (sK1 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l24 (sK1 ◇ (sK0 ◇ sK0)) sK1 sK0 X0]
    conv => enter [1]; rw [l33 sK1 sK0 X0 X1]
  have l35 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l34 sK1 sK0 X0 X1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l37 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l19 sK0 sK1]
  have l38 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l37 sK2 sK1 sK0]
    conv => enter [1]; rw [← h54067 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l39 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l10 sK0 sK2 sK1]
    conv => enter [1]; rw [← l38 sK2 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l44 sK0 X0 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l45 sK0 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0) sK1]
  have l49 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h54067 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [l40 sK0 sK1]
  have l50 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l49 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l24 X1 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l51 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l50 sK0 X0 sK0 sK1]
    conv => enter [1]; rw [← l24 X0 sK1 sK0 sK0]
  have l52 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54067 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l51 sK0 X0 sK1]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l52 sK0 X0 sK1]
  have l54 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l53 sK0 sK1 X0]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l39 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l55 x y z]

theorem Equation4512_54101_implies_Equation54067 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54101 : Equation54101 G) : Equation54067 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54101 (X0 ◇ X0) X1 X2]
    conv => enter [1, 2]; rw [← h54101 X0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54101 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54101 X0 X1 X0]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h54101 X0 X0 X0]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0]
    conv => enter [1]; rw [← h54101 X0 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h54101 X0 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l10 sK0 sK2]
    conv => enter [1]; rw [h54101 sK0 sK2 X0]
  have l12 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0 sK2]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54101 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l16 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y y z]

theorem Equation4512_54067_implies_Equation54135 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54067 : Equation54067 G) : Equation54135 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54067 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54067 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h54067 X0 X2 X0]
  have l3 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l0 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h54067 X2 X0 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l6 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ (X2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [h54067 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [h54067 sK1 X0 X1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h54067 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1]
  have l10 : ∀ X2 X0 X1 sK1 sK0 : G, (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X2 X0 X1 sK1 sK0
    conv => enter [1]; rw [← l6 sK1 X2 X0 X1]
    conv => enter [1]; rw [h54067 sK1 X2 sK0]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h54067 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2, 2]; rw [← l11 sK1]
  have l13 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l12 sK1 X0 sK1]
    conv => enter [1]; rw [l10 X0 sK1 sK1 sK1 sK0]
  have l14 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54067 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l13 sK1 X0 sK0]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l14 sK1 X0 sK0]
    conv => enter [1]; rw [h54067 sK1 (sK1 ◇ sK1) sK0]
  have l16 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [l15 sK3 sK0 sK1]
    conv => enter [1]; rw [← l15 X0 sK0 sK1]
  have l17 : ∀ X0 sK1 X2 X1 : G, ((X0 ◇ sK1) ◇ (X2 ◇ (X0 ◇ sK1))) = (X2 ◇ ((X0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1 X2 X1
    conv => enter [1]; rw [l3 (X0 ◇ sK1) X2 sK1]
    conv => enter [1, 2, 2]; rw [h54067 sK1 X0 X1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 X0]
  have l20 : ∀ X0 sK1 X2 X1 : G, ((X0 ◇ sK1) ◇ (X2 ◇ (X0 ◇ sK1))) = (X2 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 sK1 X2 X1
    conv => enter [1]; rw [l17 X0 sK1 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 X0]
  have l22 : ∀ X0 sK1 X2 : G, ((X0 ◇ sK1) ◇ (X2 ◇ (X0 ◇ sK1))) = (X2 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)))) := by
    intro X0 sK1 X2
    conv => enter [1]; rw [l20 X0 sK1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l7 sK1 X0 X0]
  have l23 : ∀ X0 sK1 X2 : G, ((X0 ◇ sK1) ◇ (X2 ◇ (X0 ◇ sK1))) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X2
    conv => enter [1]; rw [l22 X0 sK1 X2]
    conv => enter [1, 2, 2]; rw [← l21 sK1 X0]
  have l24 : ∀ X2 sK0 sK1 X0 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((X0 ◇ sK1) ◇ (X2 ◇ (X0 ◇ sK1))) := by
    intro X2 sK0 sK1 X0
    conv => enter [1]; rw [← l10 X2 X0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l23 X0 sK1 X2]
  have l25 : ∀ X2 sK0 sK1 X0 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (X2 ◇ (X0 ◇ sK1)))) := by
    intro X2 sK0 sK1 X0
    conv => enter [1]; rw [l24 X2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 sK1 (X2 ◇ (X0 ◇ sK1))]
  have l26 : ∀ X2 sK0 sK1 X0 : G, (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (X2 ◇ sK1))) := by
    intro X2 sK0 sK1 X0
    conv => enter [1]; rw [l25 X2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l5 sK1 X2 X0]
  have l27 : ∀ sK1 X0 X2 sK0 : G, (sK1 ◇ (X0 ◇ sK1)) = (X2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X2 sK0
    conv => enter [1]; rw [l3 sK1 X0 X2]
    conv => enter [1]; rw [← l26 X2 sK0 sK1 X0]
  have l28 : ∀ sK3 sK0 sK1 X0 : G, (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK3 sK0 sK1 X0
    conv => enter [1]; rw [← l27 sK1 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l28 z w x y]

theorem Equation4512_54135_implies_Equation54067 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54135 : Equation54135 G) : Equation54067 G := by
  have l0 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l0 sK2 sK0]
    conv => enter [1, 2]; rw [h54135 sK0 sK0 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h54135 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [h54135 sK0 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h54135 sK0 sK0 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK2]
    conv => enter [1]; rw [← l1 sK2 sK0 sK1]
  have l4 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← h54135 sK0 (sK2 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l4 X0 X1 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54135 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

end Semigroup5
