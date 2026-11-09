import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41726_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation54270 G := by
  have l0 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ sK2)]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK2)) sK2 X0]
    conv => enter [1, 1]; rw [l1 sK1 sK2]
  have l3 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK2 ◇ sK2) X0]
  have l4 : ∀ sK2 X0 X1 X2 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X0 X1 X2 sK1
    conv => enter [1]; rw [h41726 sK2 X0 X1 X2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK1 sK2]
  have l5 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h41726 (X1 ◇ (X2 ◇ X0)) X3 X4 X1 X1]
    conv => enter [1, 2, 2]; rw [← h41726 X0 X1 X1 X1 X2]
  have l6 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l5 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2 sK2 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41726 (sK2 ◇ sK2) sK2 sK2 sK2 (sK2 ◇ sK2)]
  have l8 : ∀ X0 X3 X4 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X4
    conv => enter [1]; rw [h41726 X0 X0 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← l6 X3 X4 X0 X0 X0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l7 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h41726 (sK2 ◇ sK2) X0 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [← h41726 sK2 sK2 sK2 sK2 sK2]
  have l11 : ∀ sK2 X3 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ (sK2 ◇ sK2))) ◇ X3)) := by
    intro sK2 X3 X0 X1 X2
    conv => enter [1, 1]; rw [h41726 sK2 X0 X1 X2 sK2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (sK2 ◇ sK2))) X3]
  have l12 : ∀ sK2 X3 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (sK2 ◇ sK2)) ◇ X3))) := by
    intro sK2 X3 X0 X1 X2
    conv => enter [1]; rw [l11 sK2 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (sK2 ◇ sK2)) X3]
  have l13 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l7 sK2]
    conv => enter [1]; rw [l10 sK2 X0]
  have l14 : ∀ sK2 X3 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((sK2 ◇ sK2) ◇ X3)))) := by
    intro sK2 X3 X0 X1 X2
    conv => enter [1]; rw [l12 sK2 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (sK2 ◇ sK2) X3]
  have l15 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l13 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l16 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l13 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l9 sK1 sK2]
  have l17 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l16 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 X0]
  have l18 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l15 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK2 X0 sK2]
  have l19 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41726 sK2 X0 sK2 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 (sK1 ◇ sK2)]
  have l20 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l19 sK2 sK2 sK1]
    conv => enter [1]; rw [← l15 sK2 (sK1 ◇ sK2) sK2]
  have l21 : ∀ X0 X4 : G, (X0 ◇ X0) = (X4 ◇ (X0 ◇ X0)) := by
    intro X0 X4
    conv => enter [1]; rw [h41726 X0 (X0 ◇ X0) X0 X0 X0]
    conv => enter [1]; rw [l15 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X4]
    conv => enter [1, 2]; rw [← h41726 X0 (X0 ◇ X0) X0 X0 X0]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l21 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1 X0]
    conv => enter [1]; rw [← h41726 X1 X0 X0 X1 X0]
  have l24 : ∀ sK2 X0 X1 X2 X3 : G, ((sK2 ◇ X0) ◇ (sK2 ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ ((sK2 ◇ sK2) ◇ X0)))) := by
    intro sK2 X0 X1 X2 X3
    conv => enter [1]; rw [h41726 (sK2 ◇ X0) X1 X2 X3 (sK2 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK2 X0]
  have l25 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ X0) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l14 sK2 X0 sK2 sK2 sK2]
    conv => enter [1]; rw [← l24 sK2 X0 sK2 sK2 sK2]
  have l26 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [l25 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 X0 (sK2 ◇ X0)]
  have l27 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l26 sK2 X0]
    conv => enter [1]; rw [l23 sK2 X0]
  have l28 : ∀ sK2 X0 X1 X2 X3 X4 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) := by
    intro sK2 X0 X1 X2 X3 X4
    conv => enter [1]; rw [l27 sK2 X0]
    conv => enter [1]; rw [h41726 X0 X1 X2 X3 X4]
  have l29 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← l8 X0 X1 X2]
  have l30 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l29 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l31 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l30 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X0) X3]
  have l32 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l31 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X3]
  have l33 : ∀ sK2 X3 X0 : G, ((sK2 ◇ sK2) ◇ X3) = (X0 ◇ (X0 ◇ X3)) := by
    intro sK2 X3 X0
    conv => enter [1]; rw [l28 sK2 X3 sK2 sK2 X0 X0]
    conv => enter [1]; rw [← l32 X0 X3 sK2 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l33 sK2 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l20 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l16 y x]
  conv => enter [1]; rw [← l34 z x y]

theorem Equation4512_41726_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation54261 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h41726 (sK1 ◇ sK1) X0 X1 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41726 sK1 sK1 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l2 sK1 sK1 sK1 sK1]
  have l4 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41726 (sK0 ◇ sK1) X0 X1 X2 sK1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h41726 (sK1 ◇ sK1) X0 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h41726 sK1 sK1 sK1 sK1 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h41726 sK1 X0 X1 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y x]
  conv => enter [1]; rw [← l8 z y]

theorem Equation4512_41726_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41726 : Equation41726 G) : Equation41529 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l6 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 (sK0 ◇ sK0) X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0]
  have l7 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41726 sK0 X0 X1 X2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0]
  have l8 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 X0 X1 X2]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1, 1]; rw [← l9 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41726 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41726 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l16 sK0]
  intro x
  conv => enter [1]; rw [l17 x]
  conv => enter [1]; rw [l11 x]

@[equational_result]
theorem Equation41580_implies_Equation41553 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41553 G := by
  intro x y z w
  conv => enter [1]; rw [h41580 x y x z w]

@[equational_result]
theorem Equation41580_implies_Equation41567 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41567 G := by
  intro x y z w
  conv => enter [1]; rw [h41580 x y z x w]

@[equational_result]
theorem Equation41580_implies_Equation41571 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41571 G := by
  intro x y z w
  conv => enter [1]; rw [h41580 x y z y w]

@[equational_result]
theorem Equation41580_implies_Equation41577 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41577 G := by
  intro x y z w
  conv => enter [1]; rw [h41580 x y z w y]

@[equational_result]
theorem Equation41580_implies_Equation41578 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41578 G := by
  intro x y z w
  conv => enter [1]; rw [h41580 x y z w z]

@[equational_result]
theorem Equation41580_implies_Equation41551 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41551 G := by
  intro x y z
  conv => enter [1]; rw [h41580 x y x z y]

theorem Equation4512_41580_implies_Equation41565 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41565 G := by
  have l0 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation41580_implies_Equation41566 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41566 G := by
  intro x y z
  conv => enter [1]; rw [h41580 x y z x z]

@[equational_result]
theorem Equation41580_implies_Equation41576 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41576 G := by
  intro x y z w
  conv => enter [1]; rw [h41580 x y z w x]

theorem Equation4512_41580_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation310 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l2 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK1 ◇ sK1) sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41580 sK1 (sK1 ◇ sK1) sK1 sK1 sK1]
    conv => enter [1]; rw [← l2 sK1 sK1 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_41580_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41548 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l1 : ∀ sK1 sK0 X0 X1 X2 X3 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK1 sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK0 ◇ (sK1 ◇ sK1)) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l2 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41580 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41580 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 (sK0 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ X0))))]
    conv => enter [1, 2]; rw [← l5 sK0 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation41580_implies_Equation41550 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41550 G := by
  intro x y z
  conv => enter [1]; rw [h41580 x y x z x]

@[equational_result]
theorem Equation41580_implies_Equation41568 (G : Type*) [Magma G] (h41580 : Equation41580 G) : Equation41568 G := by
  intro x y z
  conv => enter [1]; rw [h41580 x y z y x]

theorem Equation4512_41580_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41547 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l7 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ (X1 ◇ X2))]
  have l8 : ∀ sK1 sK0 X0 X1 X2 X3 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK1 sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 sK0 X0 X1 X2 X3]
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l9 : ∀ sK1 sK0 X0 X1 X2 X3 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK1 sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 sK0 X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l10 : ∀ sK0 sK1 X0 X1 X2 X3 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK1 ◇ sK0) X0 X1 X2 X3]
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l11 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41580 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 sK0 sK0 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41580 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0 sK1 sK0 sK0 sK0 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41580 (sK1 ◇ sK0) sK1 sK1 sK1 sK1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41580 sK1 (sK0 ◇ sK0) sK1 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41580 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1 sK1 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l35 x y]

theorem Equation4512_41580_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41557 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l4 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [l2 sK1 sK0 (X0 ◇ (X1 ◇ X2))]
  have l5 : ∀ sK1 sK0 X0 X1 X2 X3 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK1 sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK1 ◇ (sK1 ◇ sK0)) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41580 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 sK1 sK1 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41580 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 sK1 sK1 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK0) sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l16 sK1 sK0 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1, 2]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l21 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation4512_41580_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41538 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0 X1 X2]
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41580 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0 sK0 sK0 sK0]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l6 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l6 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_41580_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h41580 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h41580 X1 X0 X1 X1 (X1 ◇ X1)]
  have l6 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (X0 ◇ (X1 ◇ X2))]
  have l7 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l8 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41580 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41580 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 sK0 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))))]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41580 X0 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) X0 X0 X0]
    conv => enter [1, 2]; rw [← l18 sK0 X0 (X0 ◇ (X0 ◇ X0))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1, 2]; rw [l19 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation4512_41580_implies_Equation53877 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation53877 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK2) X0]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l6 : ∀ sK2 X0 X1 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 sK2 sK2 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (X1 ◇ X2))]
  have l7 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK2 ◇ sK2) sK2 X0 X1 X2]
    conv => enter [1]; rw [l4 sK2 (X0 ◇ (X1 ◇ X2))]
  have l8 : ∀ sK1 sK2 X0 X1 X2 X3 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK1 sK2 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK2 ◇ sK2) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK1 ◇ (sK2 ◇ sK2)) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41580 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK0 sK0 sK0]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41580 (sK1 ◇ (sK2 ◇ sK2)) sK1 sK1 sK1 sK1]
  have l12 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h41580 sK2 (sK2 ◇ sK2) sK2 sK2 sK2]
    conv => enter [1]; rw [← l7 sK2 sK2 sK2 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l11 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l12 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK2 ◇ sK2)]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l20 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 sK2]
  have l24 : ∀ X0 X1 sK0 sK1 sK2 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1, 1]; rw [l23 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X1]
  have l25 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l24 X0 X1 sK0 sK1 sK2]
  have l26 : ∀ sK2 X0 X1 X2 X3 : G, ((sK2 ◇ sK2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)) = ((sK2 ◇ sK2) ◇ X3) := by
    intro sK2 X0 X1 X2 X3
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (X0 ◇ (X1 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← l6 sK2 X0 X1 X2]
  have l27 : ∀ sK2 X3 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X3) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro sK2 X3 X0 X1 X2
    conv => enter [1]; rw [← l26 sK2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l28 : ∀ sK2 X3 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X3) := by
    intro sK2 X3
    conv => enter [1]; rw [l6 sK2 sK2 (sK2 ◇ sK2) X3]
    conv => enter [1]; rw [← l27 sK2 X3 sK2 sK2 sK2]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l28 sK2 X0]
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l25 sK0 X0 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK0 sK1 sK2 X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l31 sK0 sK0 sK0 X0]
  have l33 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l33 x y z y]

theorem Equation4512_41580_implies_Equation53881 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation53881 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
  have l1 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK2 sK0]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l7 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK0 ◇ sK2) (sK0 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [← l0 sK0 sK2 (X0 ◇ (X1 ◇ X2))]
  have l8 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [l5 sK0 sK2 (X0 ◇ (X1 ◇ X2))]
  have l9 : ∀ sK0 sK2 X0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 sK0 sK2 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ (X1 ◇ X2))]
  have l10 : ∀ sK0 sK2 X0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 sK0 (sK2 ◇ (sK0 ◇ sK2)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (X0 ◇ (X1 ◇ X2))]
  have l11 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK0 ◇ sK1) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l12 : ∀ sK0 sK2 X0 X1 X2 X3 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK2 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK2 ◇ (sK0 ◇ sK2)) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l13 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41580 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK2 sK0 sK0 sK0]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41580 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK2 sK0 sK0 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41580 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0 sK0 sK0]
  have l16 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK2 sK0 sK0 sK0]
  have l18 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l13 sK0 sK2]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l21 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l17 sK0 sK2]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l16 sK0 sK2]
    conv => enter [1]; rw [l19 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [l22 sK0 sK2]
  have l24 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l23 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l25 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l6 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l20 sK0 sK1]
  have l26 : ∀ X0 sK0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l6 X0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l18 sK0 sK2]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l28 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l28 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l30 : ∀ sK0 sK2 X0 X1 : G, (((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1, 1]; rw [l24 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) X1]
  have l31 : ∀ sK0 sK2 X0 X1 : G, (((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l30 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK2)) X0 X1]
  have l32 : ∀ sK0 sK2 X0 X1 : G, (((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) ◇ X1) = (sK0 ◇ sK0) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l31 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← l10 sK0 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0 X1]
  have l33 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l21 sK0 sK2]
    conv => enter [1]; rw [← l32 sK0 sK2 X0 X1]
  have l34 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l33 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0 X1]
  have l35 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l24 sK0 sK2 X0]
  have l36 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [l25 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) X1]
  have l37 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l36 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X1]
  have l38 : ∀ X0 X1 sK0 sK2 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l37 X0 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l29 sK0 sK2 X1 X0]
  have l39 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [l35 sK0 sK2 X1]
    conv => enter [1]; rw [← l38 X0 X1 sK0 sK2]
  have l40 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l39 X0 sK0 sK2 X1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 sK0 sK0]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l42 x y z]

theorem Equation4512_41580_implies_Equation54166 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation54166 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l2 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 sK1 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ X2))]
  have l3 : ∀ sK1 X0 X1 X2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK1 ◇ sK1) sK1 X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h41580 sK1 (sK1 ◇ sK1) sK1 sK1 sK1]
    conv => enter [1]; rw [← l3 sK1 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l9 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [h41580 sK1 sK1 X0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l10 : ∀ sK1 X0 sK0 sK2 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 sK0 sK2 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
    conv => enter [1, 1]; rw [← l9 sK1 X0 sK0 sK2]
  have l11 : ∀ sK1 X1 X0 sK0 sK2 : G, ((sK1 ◇ sK1) ◇ X1) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1))) := by
    intro sK1 X1 X0 sK0 sK2
    conv => enter [1]; rw [← l10 sK1 X0 sK0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l12 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X1
    conv => enter [1]; rw [l2 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1]; rw [← l11 sK1 X1 sK1 sK1 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l12 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l14 x y z]

theorem Equation4512_41580_implies_Equation54183 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation54183 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK0 ◇ sK1) (sK0 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [← l0 sK0 sK1 (X0 ◇ (X1 ◇ X2))]
  have l4 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41580 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (X0 ◇ (X1 ◇ X2))]
  have l5 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK2 ◇ sK2) sK2 X0 X1 X2]
    conv => enter [1]; rw [l1 sK2 (X0 ◇ (X1 ◇ X2))]
  have l6 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h41580 sK2 (sK2 ◇ sK2) sK2 sK2 sK2]
    conv => enter [1]; rw [← l5 sK2 sK2 sK2 sK2]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1 sK0 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l6 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [← l10 sK0 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l12 x z y]

theorem Equation4512_41580_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41580 : Equation41580 G) : Equation41529 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [l6 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41580 X1 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41580 X0 X1 X1 X1 X1]
  have l13 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41580 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (X1 ◇ X2))]
  have l14 : ∀ sK0 X0 X1 X2 X3 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h41580 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l15 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0 sK0 sK0 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41580 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0 sK0 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 1]; rw [← l18 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l19 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l22 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l3 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l21 sK0]
  intro x
  conv => enter [1]; rw [l25 x]
  conv => enter [1]; rw [l21 x]

theorem Equation4512_41716_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41716 sK0 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ X0)) X3 X2 X1]
    conv => enter [1, 2, 2]; rw [← h41716 X0 X1 X2 X1]
  have l2 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41716 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41716 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l3 (sK0 ◇ sK0) sK0 sK0]
  have l6 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l4 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ X0 X3 X2 : G, (X0 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X2
    conv => enter [1]; rw [l2 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l6 X3 X2 X0 X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41716 (sK1 ◇ sK0) X0 sK1 sK1]
    conv => enter [1, 2]; rw [← h41716 sK0 sK1 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK0]
  have l17 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l18 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l17 sK0 X0 sK1]
    conv => enter [1]; rw [← l17 sK0 ((sK1 ◇ sK0) ◇ X0) sK1]
  have l19 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41716 X0 X1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l17 sK0 ((sK1 ◇ sK0) ◇ X0) sK1]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 ((sK1 ◇ sK0) ◇ X0) X0]
  have l21 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l18 sK1 sK0 X0]
  have l22 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [l20 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ X0) X1]
  have l23 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l22 X0 X1 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l25 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l21 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [l24 sK0 sK0 X0 X1]
  have l26 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41716 X0 X1 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l13 sK0 (sK1 ◇ X0) sK1]
  have l27 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l26 X0 X0 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ X0) X0]
  have l28 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l27 X0 X0 sK1]
    conv => enter [1]; rw [l25 X0 sK1 X0]
  intro x y
  conv => enter [1]; rw [l28 x y]

@[equational_result]
theorem Equation41716_implies_Equation41568 (G : Type*) [Magma G] (h41716 : Equation41716 G) : Equation41568 G := by
  intro x y z
  conv => enter [1]; rw [h41716 x x y z]

theorem Equation4512_41716_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation41621 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41716 (sK1 ◇ sK0) X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X1]
    conv => enter [1, 2, 2, 2]; rw [l3 sK1 sK0]
  have l5 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ X0)) X3 X2 X1]
    conv => enter [1, 2, 2]; rw [← h41716 X0 X1 X2 X1]
  have l6 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41716 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l7 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h41716 X0 (sK1 ◇ sK0) (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [← l0 sK1 sK0 (X1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l8 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l5 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l7 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK0 sK1]
  have l10 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l8 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l9 sK1 sK0 X0]
  have l12 : ∀ X0 X3 X2 : G, (X0 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X2
    conv => enter [1]; rw [l6 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l10 X3 X2 X0 X0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l14 : ∀ sK1 sK0 X0 X1 X2 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h41716 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK1 sK0 X1]
  have l15 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l11 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l12 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK1]
  have l17 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [← l14 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l19 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l12 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l17 X0 X1 X2 sK1 sK0]
  have l20 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0 X0 X1 X2]
  have l21 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41716 sK0 X0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [l3 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK0 sK1 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l22 x y]
  conv => enter [1]; rw [l18 y x]

theorem Equation4512_41716_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation41547 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l11 : ∀ X1 X2 X0 X3 X4 X5 : G, ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ (X1 ◇ X0))) X3 X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h41716 X0 X4 X1 X2]
  have l12 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41716 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) X0 (sK1 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK1 sK0]
  have l13 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41716 (sK1 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X1]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0 sK1]
  have l14 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41716 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41716 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l16 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ X0)) X3 X2 X1]
    conv => enter [1, 2, 2]; rw [← h41716 X0 X1 X2 X1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41716 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK1]
  have l18 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41716 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41716 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l20 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41716 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X3 ◇ X0)))]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l22 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l16 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l23 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l15 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l24 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l19 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK0 sK1]
  have l25 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK1 sK0 X0 X1]
  have l26 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← l12 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l27 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1]; rw [← l11 X1 X2 X0 X3 X4 X5]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X1 ◇ X0)) (X1 ◇ (X2 ◇ (X1 ◇ X0)))]
  have l28 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l22 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l29 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l23 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK0 sK1]
  have l30 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l26 X0 sK1 sK0 X1]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l31 : ∀ X0 X3 X4 X5 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) := by
    intro X0 X3 X4 X5
    conv => enter [1]; rw [l20 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l27 X3 X4 X5 X0 X0 X0]
  have l32 : ∀ X0 X3 X2 : G, (X0 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X2
    conv => enter [1]; rw [l18 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l28 X3 X2 X0 X0]
  have l33 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l29 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l34 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l30 X0 sK1 sK0 X1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l35 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l34 X0 sK1 sK0 X1]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l35 sK1 sK1 sK0 sK1]
  have l37 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
  have l38 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [l37 sK1 sK0 X0]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l2 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l43 : ∀ sK0 sK1 X0 X1 X2 : G, (((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h41716 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l33 sK1 sK0 X1]
  have l44 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l33 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l32 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1 sK1]
  have l46 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [← l43 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l47 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l42 sK1 sK0]
    conv => enter [1]; rw [← l32 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l41 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l24 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l51 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [l46 X0 X1 X2 sK1 sK0]
    conv => enter [1]; rw [← l38 sK1 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l47 sK1 sK0]
  have l53 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l54 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l32 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l51 X0 X1 X2 sK1 sK0]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [l53 sK1 sK0]
  have l56 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [l54 sK0 sK1 X0 X1 X2]
  have l57 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [← l48 sK1 sK0]
    conv => enter [1]; rw [l56 sK1 sK0 X0 X1 X2]
  have l58 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [l57 sK1 sK0 X0 X1 X2]
  have l59 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l33 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l59 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l61 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41716 sK0 X0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK0 sK1]
    conv => enter [1]; rw [← l58 sK1 sK0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l62 x y]
  conv => enter [1]; rw [l60 y x]

@[equational_result]
theorem Equation41716_implies_Equation41557 (G : Type*) [Magma G] (h41716 : Equation41716 G) : Equation41557 G := by
  intro x y
  conv => enter [1]; rw [h41716 x x y y]

theorem Equation4512_41716_implies_Equation41628 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation41628 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41716 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41716 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_41716_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41716 sK0 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41716 X0 sK0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l6 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ X0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h41716 X0 sK1 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ sK0) sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l0 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [l3 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_41716_implies_Equation53938 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation53938 G := by
  have l0 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41716 sK1 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ X0)) X3 X2 X1]
    conv => enter [1, 2, 2]; rw [← h41716 X0 X1 X2 X1]
  have l2 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41716 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41716 X0 sK1 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (sK1 ◇ X0))]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l3 (sK1 ◇ sK1) sK1 sK1]
  have l6 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l4 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ X0 X3 X2 : G, (X0 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X2
    conv => enter [1]; rw [l2 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l6 X3 X2 X0 X0]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l10 sK2 sK1 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l13 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1 sK1 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ sK1) sK1 sK1]
  have l14 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1, 2]; rw [l12 sK1 sK0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1, 2]; rw [← l13 sK1]
  have l17 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ X1) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l16 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l18 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41716 sK1 X0 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41716 (sK0 ◇ sK1) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41716 sK1 sK0 sK0 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1 sK1]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l18 sK1 X0 sK0]
    conv => enter [1, 2, 1]; rw [← l12 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 (sK0 ◇ sK1) sK1]
  have l23 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l24 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ sK1) X0]
  have l25 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h41716 X0 X1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l23 sK1 ((sK0 ◇ sK1) ◇ X0) sK0]
  have l26 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l25 X0 X0 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 ((sK0 ◇ sK1) ◇ X0) X0]
  have l27 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) ((sK0 ◇ sK1) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l26 X0 sK1 sK0]
  have l28 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l27 sK1 sK0 X0 X1]
  have l29 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l30 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l29 X0 X1 sK1 X0]
    conv => enter [1]; rw [← l24 sK1 (X0 ◇ X1) X0]
  have l31 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h41716 X0 X1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l14 sK1 (sK0 ◇ X0) sK0]
  have l32 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l31 X0 X0 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 (sK0 ◇ X0) X0]
  have l33 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l32 X0 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 X0 X0]
  intro x y z
  conv => enter [1]; rw [← l33 y x]
  conv => enter [1]; rw [l15 y z x]

theorem Equation4512_41716_implies_Equation53959 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation53959 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 X5 : G, ((X1 ◇ (X2 ◇ (X1 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ (X1 ◇ X0))) X3 X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h41716 X0 X4 X1 X2]
  have l1 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41716 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ X0)) X3 X2 X1]
    conv => enter [1, 2, 2]; rw [← h41716 X0 X1 X2 X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h41716 X0 X2 X1 X2]
    conv => enter [1]; rw [← h41716 (X1 ◇ X0) X2 X2 X1]
  have l4 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4)) = ((X0 ◇ X0) ◇ X4) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X2 ◇ X0))) X4]
    conv => enter [1, 1]; rw [← h41716 X0 X1 X2 X3]
  have l5 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X0))) ◇ X4)) = (X0 ◇ (X0 ◇ X4)) := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [l4 X1 X2 X3 X0 X4]
    conv => enter [1]; rw [← h4512 X0 X0 X4]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l7 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l2 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l8 : ∀ X0 X3 X4 X5 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) := by
    intro X0 X3 X4 X5
    conv => enter [1]; rw [h41716 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X3 X4 X5]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X0)) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l5 X1 X2 X3 X0 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ (X2 ◇ X0)) X4]
  have l10 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l7 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l11 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X0) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l9 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X2 ◇ X0) X4]
  have l12 : ∀ X0 X3 X2 : G, (X0 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X2
    conv => enter [1]; rw [l1 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l10 X3 X2 X0 X0]
  have l13 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X4)) = (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X4]
  have l14 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ (X0 ◇ X0)) := by
    intro X0 X3
    conv => enter [1]; rw [l8 X0 X3 X0 X0]
    conv => enter [1, 2]; rw [← l12 X0 X0 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X0]
    conv => enter [1]; rw [l6 X0 X0 X1]
  have l16 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h41716 X3 X0 X1 X2]
    conv => enter [1]; rw [l14 X3 X4]
    conv => enter [1, 2]; rw [h41716 X3 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l13 x y x x x]
  conv => enter [1, 2]; rw [l16 x x x y x]
  conv => enter [1, 2, 2]; rw [l16 x x x y x]
  conv => enter [1, 2, 2]; rw [← h41716 (x ◇ y) x x x]
  conv => enter [1]; rw [← h41716 y x x (x ◇ y)]
  conv => enter [1]; rw [l15 y z]

theorem Equation4512_41716_implies_Equation54270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation54270 G := by
  have l0 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h41716 sK2 X0 (sK2 ◇ sK2) X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK2 sK2 sK2]
  have l1 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h41716 (X1 ◇ (X2 ◇ X0)) X3 X2 X1]
    conv => enter [1, 2, 2]; rw [← h41716 X0 X1 X2 X1]
  have l2 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ X3) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [h41716 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 sK2 X1 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (X1 ◇ (sK2 ◇ X0))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h41716 X0 sK2 sK2 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 (X1 ◇ (sK2 ◇ X0))]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X1 ◇ (X2 ◇ X0))]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← l3 (sK2 ◇ sK2) sK2 sK2]
  have l6 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l4 X3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l7 : ∀ X0 X3 X2 : G, (X0 ◇ X0) = (X3 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X3 X2
    conv => enter [1]; rw [l2 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← l6 X3 X2 X0 X0]
  have l8 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l5 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l5 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l5 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l11 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l10 sK1 sK2]
  have l12 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l5 sK2 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l9 sK0 sK2 sK2]
  have l13 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2 sK2 sK2]
    conv => enter [1]; rw [← l7 (sK2 ◇ sK2) sK2 sK2]
  have l14 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1, 1]; rw [l12 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
  have l15 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l5 sK2 X0]
    conv => enter [1, 2]; rw [← l13 sK2]
  have l16 : ∀ sK2 X1 X0 : G, ((sK2 ◇ sK2) ◇ X1) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1, 1]; rw [l15 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l17 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41716 sK2 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ sK2)]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41716 (sK1 ◇ sK2) X0 sK1 sK1]
    conv => enter [1, 2]; rw [← h41716 sK2 sK1 sK1 sK1]
  have l19 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l15 sK2 sK2]
    conv => enter [1]; rw [← l18 sK1 sK2 sK2]
  have l20 : ∀ sK2 X0 sK1 : G, (sK2 ◇ sK2) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l17 sK2 X0 sK1]
    conv => enter [1, 2, 1]; rw [← l11 sK2 sK1]
  have l21 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l20 sK2 sK2 sK1]
    conv => enter [1]; rw [← l16 sK2 (sK1 ◇ sK2) sK2]
  have l22 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l19 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l23 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK1
    conv => enter [1, 1]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK1 ◇ sK2) X0]
  have l24 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h41716 X0 X1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l22 sK2 ((sK1 ◇ sK2) ◇ X0) sK1]
  have l25 : ∀ X0 sK2 sK1 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l24 X0 X0 sK2 sK1]
    conv => enter [1]; rw [← l16 sK2 ((sK1 ◇ sK2) ◇ X0) X0]
  have l26 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK1 ◇ sK2) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l25 X0 sK2 sK1]
  have l27 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l26 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l28 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l27 sK2 sK1 X0 X1]
  have l29 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l23 sK2 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [l28 sK2 sK2 X0 X1]
  have l30 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ X0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h41716 X0 X1 sK0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l14 sK2 (sK0 ◇ X0) sK0]
  have l31 : ∀ X0 sK2 sK0 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l30 X0 X0 sK2 sK0]
    conv => enter [1]; rw [← l16 sK2 (sK0 ◇ X0) X0]
  have l32 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l31 X0 X0 sK0]
    conv => enter [1]; rw [l29 X0 sK0 X0]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l32 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l19 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y x]
  conv => enter [1]; rw [← l33 z x y]

theorem Equation4512_41716_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation54261 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41716 (sK0 ◇ (sK1 ◇ sK1)) X0 (sK0 ◇ sK1) X1]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41716 sK1 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l6 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h41716 X0 X1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l7 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41716 (sK1 ◇ sK1) X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK0]
  have l8 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h41716 X0 sK1 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ (sK1 ◇ X0))]
  have l9 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l7 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l10 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l8 (sK1 ◇ sK1) sK1 sK1]
  have l12 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l4 sK0 sK1 X0 X1]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l9 sK1 sK0 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l11 sK1 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)]
    conv => enter [1]; rw [l15 sK0 sK1 X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [l16 sK1 sK1 X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41716 (sK0 ◇ sK1) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41716 sK1 sK0 sK0 sK0]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l17 y x]
  conv => enter [1]; rw [← l20 z y]

theorem Equation4512_41716_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41716 : Equation41716 G) : Equation41529 G := by
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
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [l6 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [l12 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [l18 sK0]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41716 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X1]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK0]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41716 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X1]
    conv => enter [1, 2, 2, 2]; rw [← l19 sK0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41716 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l23 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41716 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l7 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41716 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X1]
    conv => enter [1]; rw [← l16 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l25 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l23 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l24 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0 sK0]
    conv => enter [1]; rw [← l25 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0]
    conv => enter [1]; rw [← l25 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l28 sK0]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l30 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l31 sK0]
    conv => enter [1, 1]; rw [l31 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 1]; rw [l31 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1, 1]; rw [← l31 sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l34 sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l33 sK0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l32 sK0]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1, 2]; rw [← l35 sK0]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1, 2]; rw [← l35 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l39 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l38 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [← l41 sK0]
  have l43 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l40 sK0]
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l44 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [← l25 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l44 sK0]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l45 sK0]
  have l47 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1, 2]; rw [← l35 sK0]
  have l48 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [← l47 sK0]
  intro x
  conv => enter [1]; rw [l48 x]
  conv => enter [1]; rw [l35 x]

theorem Equation4512_41571_implies_Equation310 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation310 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l1 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41571 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_41571_implies_Equation41548 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation41548 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h41571 X0 (sK0 ◇ sK0) X1 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41571 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X1))]
  have l5 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ (sK1 ◇ sK1)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l6 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41571 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 sK1 sK1]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 (sK0 ◇ (X0 ◇ X0))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 X0 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2]; rw [l17 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation41571_implies_Equation41568 (G : Type*) [Magma G] (h41571 : Equation41571 G) : Equation41568 G := by
  intro x y z
  conv => enter [1]; rw [h41571 x y z x]

theorem Equation4512_41571_implies_Equation41547 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation41547 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41571 X1 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK1 ◇ sK0) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0 sK0]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l1 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
  have l11 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41571 X0 X1 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1 (X1 ◇ X0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_41571_implies_Equation41557 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation41557 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 (sK0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l7 X0 X1 sK0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l1 sK1 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 sK0]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0 sK0]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l1 X0 sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_41571_implies_Equation41538 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation41538 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 sK0 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l2 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK1 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l3 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41571 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1 sK1]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l5 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l9 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4512_41571_implies_Equation41534 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h41571 X1 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0]
  have l5 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l1 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l7 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) X0]
  have l8 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1]
    conv => enter [1]; rw [← l5 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) sK0 sK1 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_41571_implies_Equation53877 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation53877 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK2) X0]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l6 : ∀ sK2 X0 X1 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h41571 sK2 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 (X0 ◇ (sK2 ◇ X1))]
  have l7 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 sK2 X0 X1 X2]
    conv => enter [1]; rw [l4 sK2 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l8 : ∀ sK1 sK2 X0 X1 X2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK2 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK1 ◇ (sK2 ◇ sK2)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK0 sK0]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41571 (sK1 ◇ (sK2 ◇ sK2)) sK1 sK1 sK1]
  have l12 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [← h41571 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l11 sK1 sK2]
  have l15 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l12 sK2]
  have l16 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l15 sK2]
    conv => enter [1]; rw [l4 sK2 sK2]
  have l17 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l16 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l18 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l17 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l18 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 (sK2 ◇ sK2)]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
  have l24 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l5 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  have l27 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l24 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 sK2]
  have l28 : ∀ X0 X1 sK0 sK1 sK2 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1, 1]; rw [l27 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X1]
  have l29 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l28 X0 X1 sK0 sK1 sK2]
  have l30 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = ((sK2 ◇ sK2) ◇ ((X0 ◇ (sK2 ◇ X1)) ◇ X2)) := by
    intro sK2 X2 X0 X1
    conv => enter [1, 1]; rw [l6 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (X0 ◇ (sK2 ◇ X1)) X2]
  have l31 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = ((sK2 ◇ sK2) ◇ (X0 ◇ ((sK2 ◇ X1) ◇ X2))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [l30 sK2 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ X1) X2]
  have l32 : ∀ sK2 X2 X0 X1 : G, ((sK2 ◇ sK2) ◇ X2) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ (X1 ◇ X2)))) := by
    intro sK2 X2 X0 X1
    conv => enter [1]; rw [l31 sK2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 X1 X2]
  have l33 : ∀ sK2 X2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK2 X2
    conv => enter [1]; rw [l6 sK2 sK2 (sK2 ◇ X2)]
    conv => enter [1]; rw [← l32 sK2 X2 sK2 sK2]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l33 sK2 X0]
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
  have l35 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l29 sK0 X0 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0 sK0 sK0 X0]
  have l38 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l37 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l38 x y z y]

theorem Equation4512_41571_implies_Equation53881 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation53881 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
  have l1 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l2 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [l1 sK2 sK0]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l4 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK2]
  have l5 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
  have l6 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [h41571 X1 sK2 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK2 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l8 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [l5 sK0 sK2 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l9 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [← l0 sK0 sK2 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l10 : ∀ sK2 sK0 X0 X1 X2 : G, (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK2 sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ sK2) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l11 : ∀ sK0 sK2 X0 X1 X2 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK2 ◇ (sK0 ◇ sK2)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l12 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h41571 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK2 sK0 sK0 sK0]
  have l13 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l10 sK2 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [← h41571 (sK2 ◇ (sK0 ◇ sK2)) sK2 sK2 sK2]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 sK0 sK0]
  have l15 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l8 sK0 sK2 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41571 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK0 sK0 sK0]
  have l16 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ X1) = (X1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l6 X1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK2) X0]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l12 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
  have l18 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1]; rw [l13 sK2 sK0]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l20 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [← l15 sK0 sK2]
  have l21 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l1 sK2 sK0]
    conv => enter [1]; rw [l18 sK2 sK0]
  have l22 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [l19 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1]; rw [l5 sK0 sK2 (sK0 ◇ sK2)]
  have l24 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l23 sK0 sK2]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l25 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l26 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l25 sK0 sK2]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0 sK2]
    conv => enter [1]; rw [l17 sK0 sK2]
  have l28 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) = (((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [l17 sK0 sK2]
  have l29 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l30 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l16 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK2 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 sK2 X0]
  have l31 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l30 sK0 sK2 X0]
    conv => enter [1]; rw [l17 sK0 sK2]
  have l32 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← l31 sK0 sK2 X0]
  have l33 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l34 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK2 X0]
    conv => enter [1]; rw [← l16 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) sK2 sK0 X0]
  have l35 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK2 X0]
    conv => enter [1]; rw [← l22 sK0 sK2]
  have l36 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l21 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← l36 sK0 sK2]
  have l38 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l37 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l39 : ∀ X0 sK0 sK2 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h41571 X0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [← l32 sK0 sK2 ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0)]
  have l40 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) X1]
    conv => enter [1, 1]; rw [← l39 X0 sK0 sK2]
  have l41 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X1)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l40 X0 sK0 sK2 X1]
  have l42 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l41 X0 X1 sK0 sK2]
    conv => enter [1, 2]; rw [l35 sK0 sK2 X1]
  have l43 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l42 X0 X1 sK0 sK2]
    conv => enter [1, 2]; rw [← l38 sK0 sK2]
  have l44 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l27 sK0 sK2]
    conv => enter [1]; rw [← l44 sK0 sK2]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l39 sK0 sK0 sK0]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

theorem Equation4512_41571_implies_Equation54166 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation54166 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l1 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41571 sK1 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ X1))]
  have l2 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← h41571 (sK1 ◇ sK1) sK1 sK1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [l3 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l9 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK1 ◇ X1)) ◇ X2)) := by
    intro sK1 X2 X0 X1
    conv => enter [1, 1]; rw [l1 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ X1)) X2]
  have l10 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ X1) ◇ X2))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l9 sK1 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ X1) X2]
  have l11 : ∀ sK1 X2 X0 X1 : G, ((sK1 ◇ sK1) ◇ X2) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X1 ◇ X2)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l10 sK1 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X1 X2]
  have l12 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l1 sK1 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 sK1 X2 sK1 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l12 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l14 x y z]

theorem Equation4512_41571_implies_Equation54183 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation54183 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l8 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro sK2 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 sK2 X0 X1 X2]
    conv => enter [1]; rw [l6 sK2 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l9 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ sK1) X0 X1 X2]
    conv => enter [1]; rw [l5 sK0 sK1 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l10 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK1 ◇ (sK0 ◇ sK1)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41571 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1 sK0 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41571 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0 sK0 sK0]
  have l13 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [← h41571 (sK2 ◇ sK2) sK2 sK2 sK2]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l16 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l13 sK2]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
  have l18 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l16 sK2]
    conv => enter [1]; rw [l6 sK2 sK2]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l20 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l18 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l22 : ∀ sK2 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l20 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l22 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l28 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [← l27 sK0 sK2]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l30 x z y]

theorem Equation4512_41571_implies_Equation41529 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41571 : Equation41571 G) : Equation41529 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [l5 sK0]
  have l10 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l11 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41571 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41571 X0 X1 X0 X1]
  have l12 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X2]
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l13 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ (sK0 ◇ sK0)) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l14 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41571 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l15 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0 sK0 sK0 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41571 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) sK0 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l15 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l10 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l19 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l22 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 1]; rw [← l23 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0]
  have l26 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l21 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l27 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← l26 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l25 sK0]
  intro x
  conv => enter [1]; rw [l29 x]
  conv => enter [1]; rw [l25 x]

@[equational_result]
theorem Equation41711_implies_Equation41605 (G : Type*) [Magma G] (h41711 : Equation41711 G) : Equation41605 G := by
  intro x y z
  conv => enter [1]; rw [h41711 x y x z]

@[equational_result]
theorem Equation41711_implies_Equation41659 (G : Type*) [Magma G] (h41711 : Equation41711 G) : Equation41659 G := by
  intro x y z
  conv => enter [1]; rw [h41711 x y z x]

theorem Equation4512_41711_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41711 : Equation41711 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41711 sK0 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41711 (X1 ◇ X0) X2 X1 X1]
    conv => enter [1, 2]; rw [← h41711 X0 X1 X1 X2]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41711 X1 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [h41711 X1 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ X1)]
  have l4 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ X0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X2 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41711 X0 sK0 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2, 2, 2]; rw [l6 sK0]
    conv => enter [1]; rw [← h41711 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) sK0 X0 X1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41711 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41711 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41711 sK0 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l14 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ (X0 ◇ X0)) := by
    intro X0 X3
    conv => enter [1]; rw [h41711 X0 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [l13 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) X3]
    conv => enter [1, 2]; rw [← h41711 X0 (X0 ◇ X0) X0 X0]
  have l15 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ X2) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [h41711 X2 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l13 sK0 (X0 ◇ (X1 ◇ X2)) X1]
  have l16 : ∀ sK0 X0 X1 X2 X3 : G, (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (X2 ◇ (X3 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [h41711 ((sK0 ◇ sK0) ◇ X0) X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← l13 sK0 X0 X1]
  have l17 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X2 sK0 X0
    conv => enter [1, 2, 2]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l16 sK0 X0 X1 X2 X1]
  have l18 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l17 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ X0)]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l15 X0 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 X1 X2 sK0 X0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 X0 X0]
  have l21 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41711 X1 X0 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← l14 (X0 ◇ X1) X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l14 (X0 ◇ X1) X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l24 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [h4512 X1 ((sK0 ◇ sK0) ◇ X0) X2]
    conv => enter [1, 1]; rw [← l20 X0 X1 sK0]
  have l25 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 sK0 X0 X2
    conv => enter [1]; rw [l24 X1 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l26 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 sK0 X0 X2
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK0) X0 X2]
    conv => enter [1]; rw [l25 X1 sK0 X0 X2]
  have l27 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l13 sK0 (X0 ◇ X2) sK0]
    conv => enter [1]; rw [l26 sK0 sK0 X0 X2]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l13 sK0 X0 X0]
    conv => enter [1]; rw [← l5 X1 X0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l28 sK0 X0 X1]
  have l30 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l29 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l31 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l30 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← l23 X1 X0]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l29 sK0 X1 sK0]
  have l33 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ X0)]
  have l34 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [l33 X0 sK1 sK0]
    conv => enter [1]; rw [l32 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ X0)]
  have l35 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l34 sK0 X0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1 X0]
  have l36 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l14 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l35 X0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l36 x y]

theorem Equation4512_41711_implies_Equation41621 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41711 : Equation41711 G) : Equation41621 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41711 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l8 sK1 sK0]
  have l10 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41711 (sK1 ◇ sK0) (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41711 (sK1 ◇ sK0) (sK1 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41711 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l6 sK1 sK0]
  have l13 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h41711 X0 (sK1 ◇ sK0) X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK0 X0]
  have l14 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41711 X1 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l15 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [h41711 X1 X0 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X1)]
  have l16 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [h41711 X1 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ X1)]
  have l17 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (sK0 ◇ X0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X2 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41711 X0 sK0 X1 X2]
  have l18 : ∀ sK1 sK0 X0 X1 X2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41711 X0 (sK1 ◇ sK0) X1 X2]
    conv => enter [1]; rw [← l3 sK1 sK0 (X1 ◇ (X2 ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l18 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK1]
  have l20 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [l17 sK0 sK1 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41711 (sK1 ◇ sK0) sK0 X0 X1]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l18 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) sK1 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 sK0 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0)]
    conv => enter [1]; rw [← l22 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0 sK0]
    conv => enter [1]; rw [← l14 (sK0 ◇ sK0) sK0 sK0]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41711 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l24 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l31 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41711 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK1 sK0]
  have l32 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l33 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l32 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l34 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← l31 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l15 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 X0 X1 sK1]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41711 (sK0 ◇ sK0) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41711 sK0 sK0 sK0 X0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l37 sK0 X0]
  have l39 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l38 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l30 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l44 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2, 2, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← h41711 ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) (sK1 ◇ sK0) X0 X1]
  have l45 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l44 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l48 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l16 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1 sK0]
    conv => enter [1]; rw [← l45 sK1 sK0 X0 X1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l47 sK0 sK1]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l48 sK1 sK0 sK1 sK1]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l49 sK0 sK1]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [← l50 sK1 sK0]
  have l53 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [h41711 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l50 sK1 sK0]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l54 sK1 sK0]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l41 sK1 sK0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) sK1]
    conv => enter [1]; rw [← l56 sK1 sK0]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 1]; rw [← l55 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41711 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l59 sK1 sK0]
  have l61 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l60 sK0 sK1 sK1 sK1]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41711 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l21 sK1 sK0 sK0 X0]
  have l63 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [l62 sK0 sK1 X0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41711 sK0 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l63 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l66 x y]
  conv => enter [1]; rw [l55 y x]

end Semigroup5
