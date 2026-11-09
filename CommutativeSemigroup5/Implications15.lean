import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4512_54009_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l1 X0 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54009 X2 X3 X0 X0 X0 X0]
  have l7 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X2) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [l6 X0 X1 sK2 X2]
    conv => enter [1]; rw [h4512 sK2 sK2 X2]
  have l8 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l9 : ∀ sK0 sK1 sK2 X2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [← l8 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK0 sK2 X2]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 X0]
  have l12 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 X0 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK0 ◇ sK1) X0]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 X0]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 X0 sK2 sK0 sK1]
  have l24 : ∀ X0 sK2 X1 sK0 sK1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 X1 sK0 sK1
    conv => enter [1, 1]; rw [l12 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X1]
  have l25 : ∀ X0 sK2 X1 sK0 sK1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 X1 sK0 sK1
    conv => enter [1]; rw [l24 X0 sK2 X1 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK0 ◇ sK1) X1]
  have l26 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X1]
    conv => enter [1]; rw [← l25 X0 sK2 X1 sK0 sK1]
  have l27 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 sK0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK2]
  have l30 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 X2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 sK2 X2]
  have l31 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l30 X0 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2 X0]
  have l32 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l31 X0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l23 X0 sK1 sK2 sK1]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y z]
  conv => enter [1]; rw [← l23 x y z y]

theorem Equation43_4512_54009_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53890 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l0 X0 sK1 (sK3 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54009 X2 X3 X0 X0 X0 X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ sK3) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l4 sK3 sK0 X0 X1]
  have l7 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l6 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l4 sK3 sK3 sK3 (sK3 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l7 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [l9 sK3 sK0]
    conv => enter [1]; rw [l3 sK1 sK3 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l9 sK3 sK0]
  have l13 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK3 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l11 sK1 sK3 sK0]
  have l14 : ∀ sK1 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l11 sK1 sK3 sK0]
    conv => enter [1]; rw [← l13 X0 X1 sK3 sK1 sK0]
  have l15 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l4 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l14 sK1 sK3 sK0 sK3 sK3]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l15 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation43_4512_54009_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53914 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h43 sK1 sK0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54009 X2 X3 X0 X0 X0 X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 (sK2 ◇ sK2) X1 X0]
    conv => enter [1]; rw [← l0 X0 X1 X1]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 (sK2 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [← l0 X0 sK2 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]
  conv => enter [1]; rw [← l5 y z y]

theorem Equation43_4512_54009_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53915 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h43 sK2 sK1]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54009 X2 X3 X0 X0 X0 X0]
  have l4 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK2 (sK3 ◇ sK0) X1 X0]
    conv => enter [1]; rw [← l0 X0 X1 X1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation43_4512_54009_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53927 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h43 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l0 X0 sK2 (sK3 ◇ (sK3 ◇ sK0))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54009 X2 X3 X0 X0 X0 X0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ sK3) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l4 sK3 sK0 X0 X1]
  have l7 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l6 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l4 sK3 sK3 sK3 (sK3 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l7 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l9 sK3 sK0]
    conv => enter [1]; rw [l3 sK2 sK3 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l9 sK3 sK0]
  have l13 : ∀ X0 X1 sK3 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK3 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 sK3 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l11 sK2 sK3 sK0]
  have l14 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l11 sK2 sK3 sK0]
    conv => enter [1]; rw [← l13 X0 X1 sK3 sK2 sK0]
  have l15 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l4 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l14 sK2 sK3 sK0 sK3 sK3]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l15 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation43_4512_54009_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53982 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK0) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [← h54009 X2 X3 X0 X0 X0 X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK3) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK3]
    conv => enter [1]; rw [l2 sK3 (sK0 ◇ sK0) X0 X1]
  have l5 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l4 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l2 sK3 sK3 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

theorem Equation43_4512_54009_implies_Equation53983 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation53983 G := by
  have l0 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l1 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK4 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK0) X0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54009 X2 X3 X2 X2 X2 X2]
    conv => enter [1]; rw [← h54009 X0 X1 X2 X2 X2 X2]
  have l3 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ sK2) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l0 sK2 sK3 sK2]
    conv => enter [1]; rw [l2 sK2 sK3 X0 X1]
  have l4 : ∀ sK4 sK1 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK4) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK4 sK1 sK0 sK4]
    conv => enter [1]; rw [l2 sK4 (sK1 ◇ sK0) X0 X1]
  have l5 : ∀ sK4 sK1 sK0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ sK4) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [l4 sK4 sK1 sK0 sK4 sK4]
    conv => enter [1]; rw [l2 sK4 sK4 sK4 (sK4 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ sK2) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK2 sK2]
    conv => enter [1]; rw [l2 sK2 sK2 sK4 (sK4 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK4 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0
    conv => enter [1]; rw [h43 sK4 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l5 sK4 sK1 sK0]
  have l8 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h43 sK2 (sK2 ◇ sK3)]
    conv => enter [1]; rw [l6 sK2 sK3 sK4 sK1 sK0]
  have l9 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l7 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l9 x y z w u]

@[equational_result]
theorem Equation54009_implies_Equation53859 (G : Type*) [Magma G] (h54009 : Equation54009 G) : Equation53859 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54009 sK0 sK1 sK0 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation43_4512_53983_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l3 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l5 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l4 X0 X1 sK0 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 X2]
  have l6 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK1) sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK0 X2]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [l3 sK0 X0 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation53983_implies_Equation53864 (G : Type*) [Magma G] (h53983 : Equation53983 G) : Equation53864 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y x (y ◇ z)]

@[equational_result]
theorem Equation53983_implies_Equation53867 (G : Type*) [Magma G] (h53983 : Equation53983 G) : Equation53867 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y x (z ◇ z)]

theorem Equation43_4512_53983_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53868 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 sK1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 (sK3 ◇ sK0) X0 X1]
  have l5 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 sK1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l7 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l5 sK1 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l7 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation53983_implies_Equation53874 (G : Type*) [Magma G] (h53983 : Equation53983 G) : Equation53874 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation43_4512_53983_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53877 G := by
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
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK2) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 (sK0 ◇ sK1) (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l7 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X2) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [l6 X0 X1 sK2 X2]
    conv => enter [1]; rw [h4512 sK2 sK2 X2]
  have l8 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 (sK0 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l9 : ∀ sK0 sK1 sK2 X2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ sK2) ◇ X2) := by
    intro sK0 sK1 sK2 X2
    conv => enter [1]; rw [← l8 sK0 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 sK0 sK2 X2]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l3 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 X0]
  have l12 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 X0 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 X0]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 X0 sK2 sK0 sK1]
  have l24 : ∀ X0 sK2 X1 sK0 sK1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 X1 sK0 sK1
    conv => enter [1, 1]; rw [l12 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) X1]
  have l25 : ∀ X0 sK2 X1 sK0 sK1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK2 X1 sK0 sK1
    conv => enter [1]; rw [l24 X0 sK2 X1 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) X1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l26 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X1]
    conv => enter [1]; rw [← l25 X0 sK2 X1 sK0 sK1]
  have l27 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK2 sK0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK2]
  have l30 : ∀ X0 X1 X2 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK1 sK2
    conv => enter [1]; rw [l6 X0 X1 X2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 sK2 X2]
  have l31 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l30 X0 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2 X0]
  have l32 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l31 X0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l23 X0 sK1 sK2 sK1]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y z]
  conv => enter [1]; rw [← l23 x y z y]

theorem Equation43_4512_53983_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ sK3) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l4 sK3 sK0 X0 X1]
  have l7 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l6 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l4 sK3 sK3 sK3 (sK3 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l7 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [l9 sK3 sK0]
    conv => enter [1]; rw [l3 sK1 sK3 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l9 sK3 sK0]
  have l13 : ∀ X0 X1 sK3 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK3 sK1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK3 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l11 sK1 sK3 sK0]
  have l14 : ∀ sK1 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l11 sK1 sK3 sK0]
    conv => enter [1]; rw [← l13 X0 X1 sK3 sK1 sK0]
  have l15 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l4 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l14 sK1 sK3 sK0 sK3 sK3]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l15 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation43_4512_53983_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53914 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 (sK2 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [l0 sK2 sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [← l3 y z y]

theorem Equation43_4512_53983_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53915 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l2 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation43_4512_53983_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53927 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ sK3) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [l4 sK3 sK0 X0 X1]
  have l7 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l6 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l4 sK3 sK3 sK3 (sK3 ◇ sK0)]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK1 sK3 (sK3 ◇ sK0)]
  have l9 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l7 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l11 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [l9 sK3 sK0]
    conv => enter [1]; rw [l3 sK2 sK3 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l9 sK3 sK0]
  have l13 : ∀ X0 X1 sK3 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK3 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 sK3 (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l11 sK2 sK3 sK0]
  have l14 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l11 sK2 sK3 sK0]
    conv => enter [1]; rw [← l13 X0 X1 sK3 sK2 sK0]
  have l15 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l4 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l14 sK2 sK3 sK0 sK3 sK3]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l15 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation43_4512_53983_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53983 : Equation53983 G) : Equation53982 G := by
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
  have l4 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK0) X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l7 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = ((X2 ◇ X3) ◇ (X2 ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [l6 X0 X1 X2 X3]
    conv => enter [1]; rw [l0 X2 (X2 ◇ X3) X4]
  have l8 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2]; rw [l6 X0 X1 X2 X4]
    conv => enter [1]; rw [l5 X3 X2 (X2 ◇ X4)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 sK2 X0 X1]
  have l10 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ sK2) X0 X1]
  have l11 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK3) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l4 sK3 sK0 sK3]
    conv => enter [1]; rw [l6 sK3 (sK0 ◇ sK0) X0 X1]
  have l12 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l11 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [l6 sK3 sK3 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X2 X3 X4 sK3 sK0 : G, (X2 ◇ (X3 ◇ (X2 ◇ X4))) = (X3 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro X2 X3 X4 sK3 sK0
    conv => enter [1]; rw [← l8 X3 X2 X2 X2 X4]
    conv => enter [1, 2]; rw [l6 X2 X2 sK3 (sK3 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X2 ◇ (X4 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X4 X2 X3]
    conv => enter [1]; rw [← l1 X2 X4 (X2 ◇ X3)]
  have l17 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK3 (sK0 ◇ sK0) sK3 sK3]
    conv => enter [1]; rw [l6 sK3 sK3 sK1 (sK1 ◇ sK2)]
  have l18 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK3 sK0]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0]
  have l21 : ∀ X0 X1 X4 sK3 sK0 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X4 ◇ (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 X4 sK3 sK0
    conv => enter [1]; rw [l16 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [l15 X0 X4 X0 sK3 sK0]
  have l22 : ∀ X0 X1 X4 sK1 sK2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X4 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 X4 sK1 sK2
    conv => enter [1]; rw [l21 X0 X1 X4 X0 X0]
    conv => enter [1, 2]; rw [← l19 sK1 sK2 X0 X0]
  have l23 : ∀ X0 X1 X4 sK3 sK0 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X4) = (X4 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X4 sK3 sK0
    conv => enter [1]; rw [l22 X0 X1 X4 X0 X0]
    conv => enter [1, 2]; rw [← l17 sK3 sK0 X0 X0]
  have l24 : ∀ X0 X1 X4 sK3 sK0 : G, (X0 ◇ ((X0 ◇ X1) ◇ X4)) = (X4 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X4 sK3 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X4]
    conv => enter [1]; rw [l23 X0 X1 X4 sK3 sK0]
  have l25 : ∀ X0 X1 X4 sK3 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X4))) = (X4 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X4 sK3 sK0
    conv => enter [1, 2]; rw [h4512 X0 X1 X4]
    conv => enter [1]; rw [l24 X0 X1 X4 sK3 sK0]
  have l26 : ∀ sK3 sK0 X4 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X4 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X4
    conv => enter [1, 2]; rw [l6 sK3 (sK0 ◇ sK0) sK3 X4]
    conv => enter [1]; rw [l25 sK3 sK3 X4 sK3 sK0]
  have l27 : ∀ sK3 sK0 X4 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (X4 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0 X4
    conv => enter [1]; rw [l18 sK3 sK0]
    conv => enter [1]; rw [l26 sK3 sK0 X4]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l27 sK3 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l28 x y z w]

@[equational_result]
theorem Equation53983_implies_Equation53859 (G : Type*) [Magma G] (h53983 : Equation53983 G) : Equation53859 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53983 X2 X3 X2 X2 X2]
    conv => enter [1]; rw [← h53983 X0 X1 X2 X2 X2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation43_4512_53982_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53982 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [l6 X0 X1 sK0]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK1) sK0]
  have l11 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l7 X0 X1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l13 X0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation43_4512_53982_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53864 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53982 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK2]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ sK2)]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l3 sK0 sK1 sK1 sK2]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK1) sK1 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK1) sK1 sK2]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation43_4512_53982_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53867 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l1 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h53982 X0 X1 sK0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l0 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l2 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [l1 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l2 sK0 (sK2 ◇ sK2) sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation43_4512_53982_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53868 G := by
  have l0 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l1 : ∀ X0 X1 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK1 sK3 sK0
    conv => enter [1]; rw [h53982 X0 X1 sK1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0))]
  have l2 : ∀ X0 X1 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK1 sK3 sK0
    conv => enter [1]; rw [l1 X0 X1 sK1 sK3 sK0]
    conv => enter [1]; rw [← l0 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l2 sK1 (sK3 ◇ sK0) sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation43_4512_53982_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53874 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53982 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2 (sK1 ◇ sK2)]
  have l4 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l3 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l5 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l4 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 X0 X1]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
  have l11 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l0 X0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l11 X0 sK0 sK1 sK2]
  have l13 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation43_4512_53982_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l2 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53982 X0 X1 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l2 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l4 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK2 X0]
    conv => enter [1]; rw [l3 sK2 X0 sK1 sK2]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l4 X0 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation43_4512_53982_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l3 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l4 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK1 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53982 X0 X1 sK3 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK3 sK0 (sK3 ◇ sK0)]
  have l6 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l5 X0 X1 sK3 sK0]
  have l7 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l2 sK3 sK0 sK3]
    conv => enter [1]; rw [← l6 sK3 sK0 sK3 sK0]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 (sK1 ◇ sK2)]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l6 sK3 sK0 sK3 (sK3 ◇ sK0)]
  have l10 : ∀ sK3 sK0 : G, ((sK3 ◇ sK0) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l7 sK3 sK0]
    conv => enter [1]; rw [l6 sK3 sK0 sK3 (sK3 ◇ sK0)]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l9 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l10 sK3 sK0]
  have l13 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK3 sK0]
    conv => enter [1]; rw [l11 sK3 sK0 sK1 sK2]
  have l14 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [← l6 sK3 sK0 sK3 sK0]
    conv => enter [1]; rw [l4 sK1 (sK3 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK3 sK0 sK3 sK0]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l6 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 (sK3 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l17 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l14 sK1 sK3 sK0]
    conv => enter [1]; rw [← l16 sK1 sK2 sK3 sK0]
  have l18 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l13 sK3 sK0 sK1 sK3]
    conv => enter [1]; rw [← l17 sK1 sK3 sK0 sK3]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l18 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l19 x y z w]

theorem Equation43_4512_53982_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53914 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ X0)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK1 sK0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l4 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53982 X0 X1 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53982 X0 X1 X0 X0]
    conv => enter [1]; rw [← h53982 X2 X3 X0 X0]
  have l6 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [l0 X2 (X2 ◇ (X3 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53982 X0 X1 X2 X3]
  have l7 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l6 X2 X3 X4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ X3) X4]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l4 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l9 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l7 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 X3 X4]
  have l10 : ∀ X4 X0 X1 sK1 sK2 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X4 X0 X1 sK1 sK2
    conv => enter [1]; rw [l9 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [l8 X4 (X4 ◇ (X4 ◇ X4)) sK1 sK2]
  have l11 : ∀ sK1 sK2 X4 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X4 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 X4
    conv => enter [1]; rw [← l10 X4 sK1 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [l8 sK1 sK1 sK1 sK2]
  have l12 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l0 sK2 sK2 X0]
    conv => enter [1]; rw [l8 sK2 X0 sK1 sK2]
  have l13 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 sK1 (sK2 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l8 sK1 (sK2 ◇ sK2) sK1 sK2]
  have l14 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l12 X0 sK2 sK1]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l0 X1 X1 X0]
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
  have l16 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l15 X0 X1 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 sK1 sK2]
  have l17 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [← l16 X0 X1 sK1 sK2]
  have l18 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l14 sK1 sK2 sK1]
    conv => enter [1]; rw [l17 sK1 sK2 X0 X1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK0 sK1]
    conv => enter [1]; rw [l18 sK1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]
  conv => enter [1]; rw [← l14 y z y]

theorem Equation43_4512_53982_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53915 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK2 sK1]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l4 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [h53982 X0 X1 sK2 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0))]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53982 X0 X1 X0 X0]
    conv => enter [1]; rw [← h53982 X2 X3 X0 X0]
  have l6 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ ((X2 ◇ (X3 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [l0 X2 (X2 ◇ (X3 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53982 X0 X1 X2 X3]
  have l7 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ ((X3 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l6 X2 X3 X4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ X3) X4]
  have l8 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 X0 X1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l1 sK2 sK3 sK0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l9 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l7 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 X3 X4]
  have l10 : ∀ X4 X0 X1 sK2 sK3 sK0 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X4 X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l9 X4 X0 X1 X4 X4]
    conv => enter [1]; rw [l8 X4 (X4 ◇ (X4 ◇ X4)) sK2 sK3 sK0]
  have l11 : ∀ sK2 sK3 sK0 X4 : G, ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X4 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 sK0 X4
    conv => enter [1]; rw [← l10 X4 sK2 sK2 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [l8 sK2 sK2 sK2 sK3 sK0]
  have l12 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l8 sK2 (sK3 ◇ sK0) sK2 sK3 sK0]
    conv => enter [1]; rw [l11 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK2 (sK3 ◇ sK0) sK2 sK3 sK0]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X2 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l0 X1 X1 X0]
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
  have l14 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l13 X0 X1 X0 X0]
    conv => enter [1]; rw [l8 X0 X0 sK2 sK3 sK0]
  have l15 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l12 sK2 sK3 sK0 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l14 X0 X1 sK2 sK3 sK0]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK1 sK2]
    conv => enter [1]; rw [← l15 sK2 sK3 sK0 sK2 sK1]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation43_4512_53982_implies_Equation53927 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53927 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l2 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l3 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK3 sK0 (sK3 ◇ sK0)]
  have l4 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK3 ◇ sK0)) X0]
  have l5 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ ((sK3 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK3 sK0 sK0]
    conv => enter [1]; rw [← h53982 X0 X1 sK3 sK0]
  have l6 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK3 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53982 X0 X1 sK3 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK3 sK0 (sK3 ◇ sK0)]
  have l7 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l6 X0 X1 sK3 sK0]
  have l8 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK3 ◇ sK0) sK0]
    conv => enter [1]; rw [l5 sK3 sK0 X0 X1]
  have l9 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ sK0) := by
    intro sK3 sK0
    conv => enter [1]; rw [l7 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l8 sK3 sK0 sK3 sK3]
  have l10 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l9 sK3 sK0]
    conv => enter [1]; rw [l3 sK3 sK0]
  have l11 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l7 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0]
  have l12 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [← l10 sK3 sK0]
    conv => enter [1]; rw [l11 sK3 sK0 X0 X1]
  have l13 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ sK0)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [← l7 sK3 sK0 sK3 sK0]
    conv => enter [1]; rw [l10 sK3 sK0]
  have l14 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l7 sK3 sK0 sK3 sK0]
    conv => enter [1]; rw [l4 sK2 (sK3 ◇ (sK3 ◇ sK0)) sK3 sK0]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l7 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK3 sK0 sK3 sK0]
  have l16 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l7 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 X0 (sK3 ◇ (sK3 ◇ sK0)) (sK3 ◇ (sK3 ◇ sK0))]
  have l17 : ∀ sK3 sK0 X0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l12 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1]; rw [← l16 X0 sK1 sK2 sK3 sK0]
  have l18 : ∀ sK3 sK0 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 X0 sK1 sK2
    conv => enter [1]; rw [l13 sK3 sK0]
    conv => enter [1]; rw [l17 sK3 sK0 X0 sK1 sK2]
  have l19 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 sK1 X0 sK1 sK2]
  have l20 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l4 X0 sK2 sK3 sK0]
    conv => enter [1, 2, 2]; rw [l15 sK3 sK0 sK1 sK2]
  have l21 : ∀ sK2 sK1 X0 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 X0 sK3 sK0
    conv => enter [1, 2]; rw [l19 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 X0 sK2 sK3 sK0 sK1]
  have l22 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK2]
    conv => enter [1]; rw [l21 sK2 sK1 X0 sK3 sK0]
  have l23 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l14 sK2 sK3 sK0]
    conv => enter [1, 1]; rw [l15 sK3 sK0 sK1 sK2]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK3 sK0]
    conv => enter [1]; rw [← l23 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l24 x y z w]

theorem Equation43_4512_53982_implies_Equation53983 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53982 : Equation53982 G) : Equation53983 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK4 X0 sK1 sK0 : G, (sK4 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 X0 sK1 sK0
    conv => enter [1, 2]; rw [h43 X0 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l0 sK4 (sK4 ◇ (sK1 ◇ sK0)) X0]
  have l2 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK4 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h53982 X0 X1 sK4 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l1 sK4 (sK4 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l3 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK4 (sK4 ◇ (sK1 ◇ sK0)) (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK4 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l3 sK4 (sK1 ◇ sK0) sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation43_4512_53932_implies_Equation53878 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53932 : Equation53932 G) : Equation53878 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l2 : ∀ sK0 X0 sK3 : G, (sK0 ◇ (X0 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [h43 X0 sK3]
    conv => enter [1]; rw [l1 sK0 sK3 X0]
  have l3 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← l0 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53932 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h53932 X2 X1 X0 X0 X0]
  have l5 : ∀ sK1 sK2 X1 X2 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X2 X3
    conv => enter [1]; rw [h53932 sK1 sK2 X1 X2 X3]
  have l6 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0 X0 sK3]
    conv => enter [1, 2]; rw [l2 sK0 X0 sK3]
  have l7 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l3 sK2 X0 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l7 x y x z w]

theorem Equation43_4512_53932_implies_Equation53895 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53932 : Equation53932 G) : Equation53895 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = (X5 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    conv => enter [1]; rw [← h53932 X6 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h53932 X5 X6 X6 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53932 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h53932 X2 X1 X0 X0 X0]
  have l5 : ∀ X5 X6 X0 X1 X2 X3 X4 : G, (X5 ◇ (X5 ◇ X6)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X5 X6 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l3 X0 X1 X2 X3 X4 X5 X6]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  intro x y z w u
  conv => enter [1]; rw [l4 x y (x ◇ x)]
  conv => enter [1, 2]; rw [← h4512 x x y]
  conv => enter [1]; rw [← h4512 x x (x ◇ (x ◇ y))]
  conv => enter [1]; rw [← l5 x u x x x x y]
  conv => enter [1]; rw [h53932 x u w x z]
  conv => enter [1, 2]; rw [l2 w x z]
  conv => enter [1]; rw [l2 u x (w ◇ z)]
  conv => enter [1, 2]; rw [← l1 w z u]
  conv => enter [1, 2]; rw [← l1 z u w]
  conv => enter [1, 2, 2]; rw [h43 u w]

theorem Equation43_4512_53932_implies_Equation54009 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53932 : Equation53932 G) : Equation54009 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4))) = (X5 ◇ (X5 ◇ X6)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    conv => enter [1]; rw [← h53932 X6 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h53932 X5 X6 X6 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53932 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h53932 X2 X1 X0 X0 X0]
  have l5 : ∀ X5 X6 X0 X1 X2 X3 X4 : G, (X5 ◇ (X5 ◇ X6)) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X5 X6 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l3 X0 X1 X2 X3 X4 X5 X6]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  intro x y z w u v
  conv => enter [1]; rw [l4 x y (x ◇ x)]
  conv => enter [1, 2]; rw [← h4512 x x y]
  conv => enter [1]; rw [← h4512 x x (x ◇ (x ◇ y))]
  conv => enter [1]; rw [← l5 x u x x x x y]
  conv => enter [1]; rw [h53932 x u v w z]
  conv => enter [1, 2]; rw [← l1 w z v]
  conv => enter [1, 2]; rw [← l1 z v w]
  conv => enter [1]; rw [l2 u z (v ◇ w)]
  conv => enter [1, 2]; rw [← l1 v w u]
  conv => enter [1, 2]; rw [← l1 w u v]

theorem Equation43_4512_53927_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [h53927 X1 X2 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 X0]
  have l4 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X4) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [h4512 X3 (X3 ◇ X0) X4]
    conv => enter [1, 1]; rw [h53927 X3 X0 X1 X2]
  have l5 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l6 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l5 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l7 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4)) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l4 X3 X0 X4 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X4]
  have l8 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [l3 X1 X2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l9 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l6 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l10 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X4))) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l7 X3 X0 X4 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X2) X4]
  have l11 : ∀ X2 sK0 sK1 X0 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK1 X0
    conv => enter [1]; rw [← l8 X2 X2 sK0 sK1 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK0 sK1]
  have l12 : ∀ X4 X0 X1 X3 sK0 sK1 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X4 X0 X1 X3 sK0 sK1
    conv => enter [1]; rw [l9 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK0 sK1]
  have l13 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X4)))) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l10 X3 X0 X4 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X4]
  have l14 : ∀ X4 X0 X1 sK0 sK1 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK0 sK1 X3
    conv => enter [1]; rw [l12 X4 X0 X1 X3 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (X3 ◇ X4) (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ X3 X0 X4 X2 sK0 sK1 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((X2 ◇ X4) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X3 X0 X4 X2 sK0 sK1
    conv => enter [1]; rw [l13 X3 X0 X4 X3 X2]
    conv => enter [1, 2]; rw [h53927 X3 (X2 ◇ X4) sK0 sK1]
  have l16 : ∀ X4 X0 X1 sK0 sK1 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X4 X0 X1 sK0 sK1
    conv => enter [1]; rw [l14 X4 X0 X1 sK0 sK1 X4]
    conv => enter [1]; rw [l11 X1 sK0 sK1 (X4 ◇ X4)]
  have l17 : ∀ X3 X0 X4 sK0 sK1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X2 ◇ X4))) := by
    intro X3 X0 X4 sK0 sK1 X2
    conv => enter [1]; rw [l15 X3 X0 X4 X2 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (X2 ◇ X4) (sK0 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ X1 sK0 sK1 X4 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X4 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK0 sK1 X4
    conv => enter [1]; rw [← l16 X4 X1 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK0 sK1]
  have l19 : ∀ X0 sK0 sK1 X3 X4 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X3 ◇ ((X3 ◇ X0) ◇ X4)) := by
    intro X0 sK0 sK1 X3 X4
    conv => enter [1]; rw [← l11 X0 sK0 sK1 (X0 ◇ X4)]
    conv => enter [1]; rw [← l17 X3 X0 X4 sK0 sK1 X0]
  have l20 : ∀ X0 sK0 sK1 X3 X4 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X3 ◇ (X3 ◇ (X0 ◇ X4))) := by
    intro X0 sK0 sK1 X3 X4
    conv => enter [1]; rw [l19 X0 sK0 sK1 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X0 X4]
  have l21 : ∀ X0 sK0 sK1 X4 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((X0 ◇ X4) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X4
    conv => enter [1]; rw [l20 X0 sK0 sK1 X0 X4]
    conv => enter [1]; rw [h53927 X0 (X0 ◇ X4) sK0 sK1]
  have l22 : ∀ X0 sK0 sK1 X4 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X4)) := by
    intro X0 sK0 sK1 X4
    conv => enter [1]; rw [l21 X0 sK0 sK1 X4]
    conv => enter [1]; rw [h43 (X0 ◇ X4) (sK0 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 (sK0 ◇ sK0) sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l24 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53927 X0 X1 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l22 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 X0]
  have l25 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l24 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 X1]
  have l26 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l25 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 (sK0 ◇ sK0) sK0 sK1]
  have l29 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 (sK0 ◇ sK0) sK0 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l29 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation43_4512_53927_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK1 ◇ sK2)]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
  have l9 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l10 : ∀ X1 X2 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro X1 X2 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53927 X1 X2 sK0 (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 sK2 X0]
  have l11 : ∀ X1 X2 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro X1 X2 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l10 X1 X2 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l12 : ∀ X2 sK0 sK1 sK2 X0 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X2 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l11 X2 X2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK0 (sK1 ◇ sK2)]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53927 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK2) sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l9 sK1 sK0 sK2]
  have l14 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l12 sK1 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l14 sK1 sK2 sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53927 sK0 (sK1 ◇ sK2) sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l15 sK1 sK0 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53927 sK0 sK1 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l16 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l17 x y z]

theorem Equation43_4512_53927_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK2 ◇ sK2))]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l4 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [h53927 X1 X2 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l8 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [h53927 X1 X2 sK0 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK2 X0]
  have l9 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l10 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l9 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l11 : ∀ X1 X2 sK0 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro X1 X2 sK0 sK2 X0
    conv => enter [1]; rw [l8 X1 X2 sK0 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK2)) X0]
  have l12 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [l7 X1 X2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l13 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l10 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l14 : ∀ X1 sK0 sK2 sK1 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK0 sK2 sK1
    conv => enter [1]; rw [← h53927 X1 X1 sK0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h53927 X1 X1 sK0 sK1]
  have l15 : ∀ X2 sK0 sK2 X0 sK1 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l11 X2 X2 sK0 sK2 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK0 sK1]
  have l16 : ∀ X2 sK0 sK1 X0 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK1 X0
    conv => enter [1]; rw [← l12 X2 X2 sK0 sK1 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK0 sK1]
  have l17 : ∀ X4 X0 X1 X3 sK0 sK1 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X4 X0 X1 X3 sK0 sK1
    conv => enter [1]; rw [l13 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK0 sK1]
  have l18 : ∀ X4 X0 X1 sK0 sK1 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK0 sK1 X3
    conv => enter [1]; rw [l17 X4 X0 X1 X3 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (X3 ◇ X4) (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ X4 X0 X1 sK0 sK1 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X4 X0 X1 sK0 sK1
    conv => enter [1]; rw [l18 X4 X0 X1 sK0 sK1 X4]
    conv => enter [1]; rw [l16 X1 sK0 sK1 (X4 ◇ X4)]
  have l20 : ∀ X1 sK0 sK1 X4 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X4 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK0 sK1 X4
    conv => enter [1]; rw [← l19 X4 X1 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK0 sK1]
  have l21 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1]; rw [l14 X0 sK0 sK2 sK1]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l14 sK1 sK0 sK2 sK1]
  have l23 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l14 sK2 sK0 sK2 sK1]
  have l24 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [l14 (sK2 ◇ sK2) sK0 sK2 sK1]
  have l25 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l20 (sK2 ◇ sK2) sK0 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 sK2 sK1]
  have l26 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [← l20 sK2 sK0 sK1 sK2]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2]
  have l28 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l25 sK2 sK0 sK1]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK2 ◇ sK2)) sK0 sK2 sK1]
  have l29 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l14 (sK2 ◇ sK2) sK0 sK2 sK1]
    conv => enter [1]; rw [l26 sK2 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0 sK1]
    conv => enter [1]; rw [l14 (sK0 ◇ sK1) sK0 sK1 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l28 sK2 sK0 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l29 sK2 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 (sK0 ◇ sK1) sK0 sK2 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l21 sK0 sK2 sK1 sK1]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK0 sK1 sK1]
  have l41 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l16 (sK0 ◇ sK1) sK0 sK1 X0]
    conv => enter [1]; rw [← l41 sK0 sK1 X0]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l43 sK0 sK1 X0]
    conv => enter [1]; rw [h53927 (sK0 ◇ sK1) X0 sK0 sK1]
  have l45 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53927 X0 X1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l38 sK0 sK1 sK2]
  have l46 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l45 X0 X1 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l0 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l47 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l46 X0 X1 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l16 sK2 sK0 sK1 (sK0 ◇ sK1)]
  have l48 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l47 X0 X1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l20 sK2 sK0 sK1 X1]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l40 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1 X0]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l48 sK0 sK1 sK2 sK0 sK1]
  have l51 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l48 sK0 (sK2 ◇ sK2) sK2 sK0 sK1]
    conv => enter [1]; rw [← l49 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l54 x y z]

theorem Equation43_4512_53927_implies_Equation53868 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53868 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l2 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [h53927 X1 X2 sK1 (X0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK2 X0]
  have l3 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l5 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [l2 X1 X2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l6 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l4 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l7 : ∀ X1 sK1 sK3 sK0 sK2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← h53927 X1 X1 sK1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h53927 X1 X1 sK1 sK2]
  have l8 : ∀ X2 sK1 sK2 X0 : G, (X2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X2 sK1 sK2 X0
    conv => enter [1]; rw [← l5 X2 X2 sK1 sK2 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK1 sK2]
  have l9 : ∀ X4 X0 X1 X3 sK1 sK2 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X4 X0 X1 X3 sK1 sK2
    conv => enter [1]; rw [l6 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK1 sK2]
  have l10 : ∀ X4 X0 X1 sK1 sK2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK1 sK2 X3
    conv => enter [1]; rw [l9 X4 X0 X1 X3 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (X3 ◇ X4) (sK1 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ X4 X0 X1 sK1 sK2 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X4 X0 X1 sK1 sK2
    conv => enter [1]; rw [l10 X4 X0 X1 sK1 sK2 X4]
    conv => enter [1]; rw [l8 X1 sK1 sK2 (X4 ◇ X4)]
  have l12 : ∀ X1 sK1 sK2 X4 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X4 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X1 sK1 sK2 X4
    conv => enter [1]; rw [← l11 X4 X1 X1 sK1 sK2]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK1 sK2]
  have l13 : ∀ X1 X0 sK1 sK3 sK0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro X1 X0 sK1 sK3 sK0
    conv => enter [1]; rw [l0 X1 X0 X1]
    conv => enter [1]; rw [h53927 X1 X0 sK1 (sK1 ◇ (sK3 ◇ sK0))]
  have l14 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [l13 X1 X0 sK1 X1 X1]
    conv => enter [1, 2]; rw [l7 sK1 sK1 X1 X1 sK2]
  have l15 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l12 sK1 sK1 sK2 X0]
    conv => enter [1]; rw [← l14 X1 X0 sK1 sK2]
  have l16 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← l15 sK1 sK2 sK1 sK2]
  have l17 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l0 sK1 (sK3 ◇ sK0) sK1]
    conv => enter [1]; rw [← l15 sK1 sK2 sK1 (sK3 ◇ sK0)]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l16 sK1 sK2]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1]; rw [← l17 sK1 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l19 x y z w]

theorem Equation43_4512_53927_implies_Equation53874 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53874 G := by
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
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 (sK1 ◇ sK2)]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK2 ◇ X0) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [h53927 sK1 (sK2 ◇ X0) sK1 sK2]
  have l6 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h53927 (sK0 ◇ sK1) sK2 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l7 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h53927 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l1 X1 X1 X0]
  have l8 : ∀ X0 X1 sK1 sK2 X2 : G, ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X2 ◇ (X2 ◇ X0)) := by
    intro X0 X1 sK1 sK2 X2
    conv => enter [1]; rw [← h53927 X0 (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← h53927 X2 X0 X0 X1]
  have l9 : ∀ X0 sK1 sK2 X2 X3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 sK1 sK2 X2 X3
    conv => enter [1]; rw [← h53927 X0 X0 sK1 sK2]
    conv => enter [1]; rw [h53927 X0 X0 X2 X3]
  have l10 : ∀ X0 sK1 sK2 X3 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X3 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2 X3
    conv => enter [1]; rw [l9 X0 sK1 sK2 X0 X3]
    conv => enter [1, 2]; rw [h53927 X0 X3 sK1 sK2]
  have l11 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← h53927 X0 X0 sK1 sK2]
    conv => enter [1]; rw [← l8 X0 X1 sK1 sK2 X0]
  have l12 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l13 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ X0) (sK1 ◇ (sK1 ◇ sK2))]
  have l14 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53927 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [h43 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l15 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l11 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) (sK1 ◇ (sK1 ◇ sK2))]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l12 sK2 sK1 sK0]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l13 sK1 sK2 X0]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l19 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l17 sK1 sK2 X0]
    conv => enter [1]; rw [← l15 sK2 sK1 sK2 X0]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l19 sK1 sK2 X0]
    conv => enter [1]; rw [h43 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l21 sK1 sK2 X0]
    conv => enter [1]; rw [l4 sK1 sK2]
  have l23 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [h53927 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l24 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [h53927 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l25 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [← l22 sK1 sK2 X0]
    conv => enter [1]; rw [← l24 X0 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l23 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l7 sK1 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l25 sK1 sK2 X0 sK0]
  have l28 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l26 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l10 sK1 sK1 sK2 X0]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53927 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [l27 sK1 sK0 X0 sK0]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53927 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1 X0 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l20 sK1 sK2 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l31 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l32 x y z]

theorem Equation43_4512_53927_implies_Equation53877 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53877 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l4 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [h53927 X1 X2 sK0 (X0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 X0]
  have l5 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l6 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l5 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l7 : ∀ X1 X2 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 X2 sK0 sK1 X0
    conv => enter [1]; rw [l4 X1 X2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l8 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l6 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l9 : ∀ X2 sK0 sK1 X0 : G, (X2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X2 sK0 sK1 X0
    conv => enter [1]; rw [← l7 X2 X2 sK0 sK1 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK0 sK1]
  have l10 : ∀ X4 X0 X1 X3 sK0 sK1 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X4 X0 X1 X3 sK0 sK1
    conv => enter [1]; rw [l8 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK0 sK1]
  have l11 : ∀ X4 X0 X1 sK0 sK1 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK0 sK1 X3
    conv => enter [1]; rw [l10 X4 X0 X1 X3 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (X3 ◇ X4) (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ X4 X0 X1 sK0 sK1 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X4 X0 X1 sK0 sK1
    conv => enter [1]; rw [l11 X4 X0 X1 sK0 sK1 X4]
    conv => enter [1]; rw [l9 X1 sK0 sK1 (X4 ◇ X4)]
  have l13 : ∀ X1 sK0 sK1 X4 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X4 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK0 sK1 X4
    conv => enter [1]; rw [← l12 X4 X1 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h53927 sK0 ((sK0 ◇ sK1) ◇ X0) sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53927 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  have l16 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h53927 sK2 X0 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← h53927 sK0 (sK0 ◇ sK1) sK0 sK1]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l13 X0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l20 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53927 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK0 sK1 X0]
    conv => enter [1]; rw [← l22 X0 sK0 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  have l26 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l16 sK2 X0 sK0 sK1]
  have l27 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l26 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l13 X0 sK0 sK1 sK1]
  have l28 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← l27 X0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l28 x y x z]

theorem Equation43_4512_53927_implies_Equation53890 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53890 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ sK0) ◇ X0) = (sK3 ◇ (X0 ◇ sK0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l2 : ∀ X1 X2 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK3 ◇ ((sK3 ◇ sK0) ◇ X0))) := by
    intro X1 X2 sK3 sK0 X0
    conv => enter [1]; rw [h53927 X1 X2 sK3 (X0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK3 sK0 X0]
  have l3 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X4) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [h4512 X3 (X3 ◇ X0) X4]
    conv => enter [1, 1]; rw [h53927 X3 X0 X1 X2]
  have l4 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4)) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l3 X3 X0 X4 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X4]
  have l5 : ∀ X1 X2 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X1 X2 sK3 sK0 X0
    conv => enter [1]; rw [l2 X1 X2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK3 (sK3 ◇ sK0) X0]
  have l6 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X4))) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l4 X3 X0 X4 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X2) X4]
  have l7 : ∀ X2 sK3 sK0 X0 : G, (X2 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ X0)) = (X2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X2 sK3 sK0 X0
    conv => enter [1]; rw [← l5 X2 X2 sK3 sK0 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK3 sK0]
  have l8 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X4)))) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l6 X3 X0 X4 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X4]
  have l9 : ∀ X3 X0 X4 X2 sK3 sK0 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((X2 ◇ X4) ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X3 X0 X4 X2 sK3 sK0
    conv => enter [1]; rw [l8 X3 X0 X4 X3 X2]
    conv => enter [1, 2]; rw [h53927 X3 (X2 ◇ X4) sK3 sK0]
  have l10 : ∀ X3 X0 X4 sK3 sK0 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X2 ◇ X4))) := by
    intro X3 X0 X4 sK3 sK0 X2
    conv => enter [1]; rw [l9 X3 X0 X4 X2 sK3 sK0]
    conv => enter [1, 2]; rw [h43 (X2 ◇ X4) (sK3 ◇ (sK3 ◇ sK0))]
  have l11 : ∀ X0 sK3 sK0 X3 X4 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X3 ◇ ((X3 ◇ X0) ◇ X4)) := by
    intro X0 sK3 sK0 X3 X4
    conv => enter [1]; rw [← l7 X0 sK3 sK0 (X0 ◇ X4)]
    conv => enter [1]; rw [← l10 X3 X0 X4 sK3 sK0 X0]
  have l12 : ∀ X0 sK3 sK0 X3 X4 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X3 ◇ (X3 ◇ (X0 ◇ X4))) := by
    intro X0 sK3 sK0 X3 X4
    conv => enter [1]; rw [l11 X0 sK3 sK0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X0 X4]
  have l13 : ∀ X0 sK3 sK0 X4 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((X0 ◇ X4) ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK3 sK0 X4
    conv => enter [1]; rw [l12 X0 sK3 sK0 X0 X4]
    conv => enter [1]; rw [h53927 X0 (X0 ◇ X4) sK3 sK0]
  have l14 : ∀ X0 sK3 sK0 X4 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X4)) := by
    intro X0 sK3 sK0 X4
    conv => enter [1]; rw [l13 X0 sK3 sK0 X4]
    conv => enter [1]; rw [h43 (X0 ◇ X4) (sK3 ◇ (sK3 ◇ sK0))]
  have l15 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l14 sK1 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l0 (sK3 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) X0]
  have l16 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l14 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) sK3 sK0 X0]
    conv => enter [1]; rw [← l15 X0 sK1 sK3 sK0]
  have l17 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [← l16 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) (sK3 ◇ (sK3 ◇ sK0))]
  have l18 : ∀ sK1 sK3 sK0 X0 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK3 sK0 (sK3 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [← l17 X0 sK1 sK3 sK0]
  have l19 : ∀ X0 X1 X2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 X2 sK1 sK3 sK0
    conv => enter [1]; rw [h53927 X0 X1 X2 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l18 sK1 sK3 sK0 X2]
  have l20 : ∀ X0 X1 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK1 sK3 sK0
    conv => enter [1]; rw [l19 X0 X1 X0 sK1 sK3 sK0]
    conv => enter [1, 2]; rw [← l18 sK1 sK3 sK0 X0]
  have l21 : ∀ sK1 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l18 sK1 sK3 sK0 X1]
    conv => enter [1]; rw [← l20 X0 X1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l21 x z w x y]

theorem Equation43_4512_53927_implies_Equation53914 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53914 G := by
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
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK0]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK1) X0]
  have l9 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [h53927 X1 X2 sK1 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l4 sK1 sK2 X0]
  have l10 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X4) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [h4512 X3 (X3 ◇ X0) X4]
    conv => enter [1, 1]; rw [h53927 X3 X0 X1 X2]
  have l11 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l12 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l11 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l13 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X4)) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l10 X3 X0 X4 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X4]
  have l14 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [l9 X1 X2 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l15 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l12 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l16 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X4))) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l13 X3 X0 X4 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X2) X4]
  have l17 : ∀ X2 sK1 sK2 X0 : G, (X2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X2 sK1 sK2 X0
    conv => enter [1]; rw [← l14 X2 X2 sK1 sK2 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK1 (sK2 ◇ sK2)]
  have l18 : ∀ X4 X0 X1 X3 sK1 sK2 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X4 X0 X1 X3 sK1 sK2
    conv => enter [1]; rw [l15 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK1 (sK2 ◇ sK2)]
  have l19 : ∀ X3 X0 X4 X1 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X4)))) := by
    intro X3 X0 X4 X1 X2
    conv => enter [1]; rw [l16 X3 X0 X4 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X4]
  have l20 : ∀ X4 X0 X1 sK1 sK2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK1 sK2 X3
    conv => enter [1]; rw [l18 X4 X0 X1 X3 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (X3 ◇ X4) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l21 : ∀ X3 X0 X4 X2 sK1 sK2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((X2 ◇ X4) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X3 X0 X4 X2 sK1 sK2
    conv => enter [1]; rw [l19 X3 X0 X4 X3 X2]
    conv => enter [1, 2]; rw [h53927 X3 (X2 ◇ X4) sK1 (sK2 ◇ sK2)]
  have l22 : ∀ X4 X0 X1 sK1 sK2 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X4 X0 X1 sK1 sK2
    conv => enter [1]; rw [l20 X4 X0 X1 sK1 sK2 X4]
    conv => enter [1]; rw [l17 X1 sK1 sK2 (X4 ◇ X4)]
  have l23 : ∀ X3 X0 X4 sK1 sK2 X2 : G, (X3 ◇ ((X3 ◇ X0) ◇ X4)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X2 ◇ X4))) := by
    intro X3 X0 X4 sK1 sK2 X2
    conv => enter [1]; rw [l21 X3 X0 X4 X2 sK1 sK2]
    conv => enter [1, 2]; rw [h43 (X2 ◇ X4) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l24 : ∀ X1 sK1 sK2 X4 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X4 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X1 sK1 sK2 X4
    conv => enter [1]; rw [← l22 X4 X1 X1 sK1 sK2]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK1 (sK2 ◇ sK2)]
  have l25 : ∀ X0 sK1 sK2 X3 X4 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X3 ◇ ((X3 ◇ X0) ◇ X4)) := by
    intro X0 sK1 sK2 X3 X4
    conv => enter [1]; rw [← l17 X0 sK1 sK2 (X0 ◇ X4)]
    conv => enter [1]; rw [← l23 X3 X0 X4 sK1 sK2 X0]
  have l26 : ∀ X0 sK1 sK2 X3 X4 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X3 ◇ (X3 ◇ (X0 ◇ X4))) := by
    intro X0 sK1 sK2 X3 X4
    conv => enter [1]; rw [l25 X0 sK1 sK2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X3 X0 X4]
  have l27 : ∀ X0 sK1 sK2 X4 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((X0 ◇ X4) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2 X4
    conv => enter [1]; rw [l26 X0 sK1 sK2 X0 X4]
    conv => enter [1]; rw [h53927 X0 (X0 ◇ X4) sK1 (sK2 ◇ sK2)]
  have l28 : ∀ X0 sK1 sK2 X4 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X4)) := by
    intro X0 sK1 sK2 X4
    conv => enter [1]; rw [l27 X0 sK1 sK2 X4]
    conv => enter [1]; rw [h43 (X0 ◇ X4) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l29 : ∀ X3 X0 X1 X2 sK1 sK2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = ((X3 ◇ X0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X3 X0 X1 X2 sK1 sK2
    conv => enter [1, 2]; rw [← h53927 X3 X0 X1 X2]
    conv => enter [1]; rw [h53927 X3 (X3 ◇ X0) sK1 (sK2 ◇ sK2)]
  have l30 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK1) ◇ X0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h53927 sK0 ((sK0 ◇ sK1) ◇ X0) sK1 (sK2 ◇ sK2)]
  have l31 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((X0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [h53927 sK0 (X0 ◇ (sK0 ◇ sK1)) sK1 (sK2 ◇ sK2)]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53927 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ sK2)) sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l7 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h53927 sK0 X0 sK1 (sK2 ◇ sK2)]
  have l34 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [← l2 sK2 sK2 X0]
    conv => enter [1]; rw [h53927 sK2 X0 sK1 (sK2 ◇ sK2)]
  have l35 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h53927 sK2 X0 sK1 (sK2 ◇ sK2)]
  have l36 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l33 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l24 X0 sK1 sK2 sK1]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK0 ◇ sK1)]
  have l38 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l34 sK1 sK2 sK1]
    conv => enter [1]; rw [h53927 sK1 (sK1 ◇ (sK2 ◇ sK2)) sK1 (sK2 ◇ sK2)]
  have l39 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l31 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [h43 (X0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l40 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l30 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [h43 ((sK0 ◇ sK1) ◇ X0) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l41 : ∀ X3 X0 X1 X2 sK1 sK2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X3 ◇ X0)) := by
    intro X3 X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l29 X3 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [h43 (X3 ◇ X0) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l42 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l34 X0 sK2 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 X0 sK2]
  have l43 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK0]
    conv => enter [1]; rw [l17 sK0 sK1 sK2 (sK0 ◇ sK1)]
  have l44 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l38 sK1 sK2]
    conv => enter [1]; rw [← l35 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l45 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l39 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0 (sK0 ◇ sK1)]
  have l46 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l40 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK1) X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  have l47 : ∀ X3 X0 X1 X2 sK1 sK2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X3 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X3 X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [l41 X3 X0 X1 X2 sK1 sK2]
    conv => enter [1]; rw [← l28 X3 sK1 sK2 X0]
  have l48 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l42 X0 sK2 sK0 sK1]
  have l49 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l34 sK0 sK2 sK1]
    conv => enter [1]; rw [← l43 sK1 sK2 sK0]
  have l50 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l17 (sK0 ◇ sK1) sK1 sK2 X0]
    conv => enter [1]; rw [← l45 sK0 sK1 X0 sK2]
  have l51 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l24 X0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l46 sK0 sK1 X0 sK2]
  have l52 : ∀ X3 X0 X1 X2 sK2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X3 ◇ (sK2 ◇ sK2)) := by
    intro X3 X0 X1 X2 sK2
    conv => enter [1]; rw [l47 X3 X0 X1 X2 X3 sK2]
    conv => enter [1]; rw [← l34 X3 sK2 X3]
  have l53 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← l48 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 X0 sK1]
  have l54 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l49 sK0 sK2 sK1]
    conv => enter [1]; rw [← l35 sK2 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l55 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l34 (sK0 ◇ sK1) sK2 sK1]
    conv => enter [1]; rw [l50 sK0 sK1 sK2 X0]
  have l56 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l34 X0 sK2 sK1]
    conv => enter [1]; rw [l51 X0 sK1 sK2 sK0]
  have l57 : ∀ X3 X0 X2 sK1 sK2 : G, (X3 ◇ (X0 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) = (X3 ◇ (sK2 ◇ sK2)) := by
    intro X3 X0 X2 sK1 sK2
    conv => enter [1, 2, 2]; rw [← h53927 X3 X2 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l52 X3 X0 X3 X2 sK2]
  have l58 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [← l54 sK0 sK2 sK1]
  have l59 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l53 (sK0 ◇ sK1) sK0 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1 sK0 X0]
  have l60 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l53 X0 X0 sK0 sK1]
    conv => enter [1]; rw [l56 X0 X0 sK0 sK1]
  have l61 : ∀ X3 X0 X2 sK1 sK2 sK0 : G, (X3 ◇ (X0 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) = (X3 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X3 X0 X2 sK1 sK2 sK0
    conv => enter [1]; rw [l57 X3 X0 X2 sK1 sK2]
    conv => enter [1]; rw [l53 X3 sK2 sK0 sK1]
  have l62 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l58 sK1 sK2 sK0]
    conv => enter [1]; rw [l53 sK0 sK2 sK0 sK1]
  have l63 : ∀ X3 sK0 sK1 X2 sK2 : G, (X3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X3 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X3 sK0 sK1 X2 sK2
    conv => enter [1]; rw [← l61 X3 X3 X2 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l24 X2 sK1 sK2 X3]
  have l64 : ∀ X3 sK0 sK1 X2 sK2 : G, (X3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X3 ◇ (X2 ◇ (sK2 ◇ sK2))) := by
    intro X3 sK0 sK1 X2 sK2
    conv => enter [1]; rw [l63 X3 sK0 sK1 X2 sK2]
    conv => enter [1, 2]; rw [← l34 X2 sK2 sK1]
  have l65 : ∀ X3 sK0 sK1 X2 : G, (X3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X3 sK0 sK1 X2
    conv => enter [1]; rw [l64 X3 sK0 sK1 X2 X3]
    conv => enter [1, 2]; rw [l53 X2 X3 sK0 sK1]
  have l66 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2 (sK2 ◇ sK2)]
  have l67 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l66 sK1 sK2]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
  have l68 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l67 sK1 sK2]
    conv => enter [1]; rw [← l35 sK2 (sK2 ◇ sK2) sK1]
  have l69 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l68 sK1 sK2]
    conv => enter [1]; rw [l53 (sK2 ◇ sK2) sK2 sK0 sK1]
  have l70 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l69 sK1 sK2 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ sK1))]
  have l71 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l70 sK1 sK2 sK0]
    conv => enter [1]; rw [l53 (sK0 ◇ (sK0 ◇ sK1)) sK2 sK0 sK1]
  have l72 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l73 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l74 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l62 sK1 sK2 sK0]
    conv => enter [1]; rw [h53927 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1 (sK2 ◇ sK2)]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [← l34 (sK0 ◇ (sK0 ◇ sK1)) sK2 sK1]
  have l77 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l74 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l60 X0 sK0 sK1]
  have l78 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l73 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l2 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l79 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l72 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l59 sK0 sK1 X0]
  have l80 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
    conv => enter [1]; rw [l53 (sK0 ◇ (sK0 ◇ sK1)) sK2 sK0 sK1]
  have l81 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l78 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← l65 sK0 sK0 sK1 X0]
  have l82 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l71 sK1 sK2 sK0]
    conv => enter [1]; rw [← l80 sK0 sK1 sK2]
  have l83 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l62 sK1 sK2 sK1]
    conv => enter [1]; rw [← l81 sK1 sK2 X0 sK1]
  have l84 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l82 sK1 sK2 sK0]
    conv => enter [1]; rw [l77 sK0 sK1 sK2 sK0]
  have l85 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l62 sK1 sK2 sK1]
    conv => enter [1]; rw [← l84 sK1 sK2 sK1]
  have l86 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l83 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l87 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l86 sK1 sK2 X1 sK1]
    conv => enter [1, 2]; rw [l79 sK1 sK2 sK1 sK0]
  have l88 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [l87 sK1 sK2 X1 sK0]
    conv => enter [1]; rw [← l65 X1 sK0 sK1 (sK0 ◇ sK1)]
  have l89 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53927 X0 X1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [← l28 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK2 X0]
  have l90 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l89 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l24 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1 sK2 X1]
  have l91 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l90 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l35 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK1]
  have l92 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l91 X0 X1 sK2 X0]
    conv => enter [1]; rw [← l35 sK2 (sK2 ◇ sK2) X0]
  have l93 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l92 X0 X1 sK2]
    conv => enter [1]; rw [l53 (sK2 ◇ sK2) sK2 sK0 sK1]
  have l94 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l93 X0 X1 sK2 sK0 sK1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) (sK0 ◇ (sK0 ◇ sK1))]
  have l95 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l94 X0 X1 sK0 sK1 X0]
    conv => enter [1]; rw [l53 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0 sK1]
  have l96 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l95 X0 X1 X0 sK1]
    conv => enter [1]; rw [← l88 sK1 sK2 (X0 ◇ (X0 ◇ sK1)) X0]
  have l97 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l96 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l2 X0 X1 X0]
  have l98 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h43 sK0 sK1]
    conv => enter [1]; rw [← l97 sK1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l98 x y z]
  conv => enter [1]; rw [l85 y z]

theorem Equation43_4512_53927_implies_Equation53915 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53915 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK2 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) = (sK2 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK3 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK2 sK3 sK0 sK1]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK3 sK0]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1, 2]; rw [h43 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK2) X0]
  have l8 : ∀ X1 X2 sK2 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0))) := by
    intro X1 X2 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h53927 X1 X2 sK2 (X0 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK3 sK0 X0]
  have l9 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l1 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l10 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l9 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l11 : ∀ X1 X2 sK2 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X1 X2 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l8 X1 X2 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l12 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l10 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l13 : ∀ X2 sK2 sK3 sK0 X0 : G, (X2 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X2 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l11 X2 X2 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK2 (sK3 ◇ sK0)]
  have l14 : ∀ X4 X0 X1 X3 sK2 sK3 sK0 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X4 X0 X1 X3 sK2 sK3 sK0
    conv => enter [1]; rw [l12 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK2 (sK3 ◇ sK0)]
  have l15 : ∀ X4 X0 X1 sK2 sK3 sK0 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK2 sK3 sK0 X3
    conv => enter [1]; rw [l14 X4 X0 X1 X3 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [h43 (X3 ◇ X4) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l16 : ∀ X4 X0 X1 sK2 sK3 sK0 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X4 X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [l15 X4 X0 X1 sK2 sK3 sK0 X4]
    conv => enter [1]; rw [l13 X1 sK2 sK3 sK0 (X4 ◇ X4)]
  have l17 : ∀ X1 sK2 sK3 sK0 X4 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X4 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X1 sK2 sK3 sK0 X4
    conv => enter [1]; rw [← l16 X4 X1 X1 sK2 sK3 sK0]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK2 (sK3 ◇ sK0)]
  have l18 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((X0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [h53927 sK1 (X0 ◇ (sK1 ◇ sK2)) sK2 (sK3 ◇ sK0)]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h53927 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK2 (sK3 ◇ sK0)]
  have l20 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h53927 (sK1 ◇ sK2) (sK3 ◇ sK0) sK2 (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK3 sK0]
  have l21 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h53927 sK1 X0 sK2 (sK3 ◇ sK0)]
  have l22 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [← l17 X0 sK2 sK3 sK0 sK2]
  have l23 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2)]
  have l24 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l25 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l18 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [h43 (X0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l26 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l22 sK1 sK2 X0 sK3 sK0]
  have l27 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l23 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [← l2 sK1 sK2 (sK2 ◇ (sK3 ◇ sK0))]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l29 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l25 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0 (sK1 ◇ sK2)]
  have l30 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l7 sK1 X0 sK2]
    conv => enter [1]; rw [l26 sK1 X0 sK2 sK3 sK0]
  have l31 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h53927 sK2 (sK3 ◇ sK0) sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l27 sK3 sK0 sK2 sK1]
  have l32 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1]
  have l33 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l13 (sK1 ◇ sK2) sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← l29 sK1 sK2 X0 sK3 sK0]
  have l34 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l17 (sK2 ◇ (sK3 ◇ sK0)) sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 sK2 sK3 sK0]
  have l35 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l30 (sK1 ◇ sK2) sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l33 sK1 sK2 sK1 sK1 X0]
  have l36 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l30 (sK2 ◇ (sK3 ◇ sK0)) sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l34 sK2 sK3 sK0 sK1]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l35 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l36 sK2 sK3 sK0 sK1]
  have l38 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h43 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK2))]
  have l39 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l31 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l38 sK1 sK2 sK3 sK0]
  have l40 : ∀ X0 X1 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h53927 X0 X1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l39 sK2 sK3 sK0 sK1]
  have l41 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l17 (sK1 ◇ sK2) sK2 sK3 sK0 X1]
    conv => enter [1]; rw [← l40 X0 X1 sK1 sK2 sK3 sK0]
  have l42 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l30 (sK1 ◇ sK2) sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l41 sK1 sK2 sK1 sK1 X0 X1]
  have l43 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l39 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l42 sK2 sK2 X0 X1]
  have l44 : ∀ sK2 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l43 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1 X0]
  have l45 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [h43 sK1 sK2]
    conv => enter [1]; rw [← l44 sK2 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l45 x y z w]

theorem Equation43_4512_53927_implies_Equation53982 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53927 : Equation53927 G) : Equation53982 G := by
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
  have l3 : ∀ sK3 sK0 X0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK3 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l6 : ∀ X1 X2 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (sK3 ◇ ((sK3 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro X1 X2 sK3 sK0 X0
    conv => enter [1]; rw [h53927 X1 X2 sK3 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l3 sK3 sK0 X0]
  have l7 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = ((X0 ◇ (X0 ◇ X1)) ◇ X4) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 1]; rw [← h53927 X0 X1 X2 X3]
  have l8 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l1 X1 (X2 ◇ (X2 ◇ X3)) X4]
    conv => enter [1, 2]; rw [← h53927 X0 X1 X2 X3]
  have l9 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [← l8 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X3) X4]
  have l10 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X0 ◇ ((X0 ◇ X1) ◇ X4)) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l7 X1 X2 X3 X4 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X4]
  have l11 : ∀ X1 X2 sK3 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro X1 X2 sK3 sK0 X0
    conv => enter [1]; rw [l6 X1 X2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK3 (sK3 ◇ (sK0 ◇ sK0)) X0]
  have l12 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l9 X4 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X4]
  have l13 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = (X0 ◇ (X0 ◇ (X1 ◇ X4))) := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [l10 X1 X2 X3 X4 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X4]
  have l14 : ∀ X2 sK3 sK0 X0 : G, (X2 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ X0)) = (X2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK3 sK0 X0
    conv => enter [1]; rw [← l11 X2 X2 sK3 sK0 X0]
    conv => enter [1]; rw [h53927 X2 X2 sK3 (sK0 ◇ sK0)]
  have l15 : ∀ X4 X0 X1 X3 sK3 sK0 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X3 ◇ X4) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro X4 X0 X1 X3 sK3 sK0
    conv => enter [1]; rw [l12 X4 X0 X1 X4 X3]
    conv => enter [1, 2]; rw [h53927 X4 (X3 ◇ X4) sK3 (sK0 ◇ sK0)]
  have l16 : ∀ X1 X2 X3 X4 sK3 sK0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = ((X1 ◇ X4) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 X4 sK3 sK0
    conv => enter [1]; rw [l13 X1 X2 X3 X4 X1]
    conv => enter [1]; rw [h53927 X1 (X1 ◇ X4) sK3 (sK0 ◇ sK0)]
  have l17 : ∀ X4 X0 X1 sK3 sK0 X3 : G, (X4 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X3 ◇ X4))) := by
    intro X4 X0 X1 sK3 sK0 X3
    conv => enter [1]; rw [l15 X4 X0 X1 X3 sK3 sK0]
    conv => enter [1]; rw [l5 X1 (X3 ◇ X4) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l18 : ∀ X1 X2 X3 X4 sK3 sK0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ X4)) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X4)) := by
    intro X1 X2 X3 X4 sK3 sK0
    conv => enter [1]; rw [l16 X1 X2 X3 X4 sK3 sK0]
    conv => enter [1]; rw [h43 (X1 ◇ X4) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ X1 sK3 sK0 X4 X0 : G, (X1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X4 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 sK3 sK0 X4 X0
    conv => enter [1]; rw [← l14 X1 sK3 sK0 (X1 ◇ X4)]
    conv => enter [1]; rw [← l17 X4 X0 X1 sK3 sK0 X1]
  have l20 : ∀ X1 X2 X3 X4 sK3 sK0 : G, (X1 ◇ (X2 ◇ ((X2 ◇ X3) ◇ X4))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X4)) := by
    intro X1 X2 X3 X4 sK3 sK0
    conv => enter [1, 2]; rw [h4512 X2 (X2 ◇ X3) X4]
    conv => enter [1]; rw [l18 X1 X2 X3 X4 sK3 sK0]
  have l21 : ∀ X1 sK3 sK0 X4 : G, (X1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X4 ◇ (X1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK3 sK0 X4
    conv => enter [1]; rw [l19 X1 sK3 sK0 X4 X1]
    conv => enter [1, 2]; rw [h53927 X1 X1 sK3 (sK0 ◇ sK0)]
  have l22 : ∀ X1 X2 X3 X4 sK3 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X4)) := by
    intro X1 X2 X3 X4 sK3 sK0
    conv => enter [1, 2, 2]; rw [h4512 X2 X3 X4]
    conv => enter [1]; rw [l20 X1 X2 X3 X4 sK3 sK0]
  have l23 : ∀ X1 X3 X4 sK3 sK0 : G, (X1 ◇ ((X3 ◇ X4) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X4)) := by
    intro X1 X3 X4 sK3 sK0
    conv => enter [1, 2]; rw [← h53927 X1 (X3 ◇ X4) sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l22 X1 X1 X3 X4 sK3 sK0]
  have l24 : ∀ X1 sK3 sK0 X3 X4 : G, (X1 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X3 ◇ X4))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X4)) := by
    intro X1 sK3 sK0 X3 X4
    conv => enter [1]; rw [l5 X1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) (X3 ◇ X4)]
    conv => enter [1]; rw [l23 X1 X3 X4 sK3 sK0]
  have l25 : ∀ X1 sK3 sK0 X4 : G, (X1 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X4)) := by
    intro X1 sK3 sK0 X4
    conv => enter [1]; rw [← l14 X1 sK3 sK0 (X1 ◇ X4)]
    conv => enter [1]; rw [l24 X1 sK3 sK0 X1 X4]
  have l26 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53927 X0 X1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2]; rw [← l25 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) sK3 sK0 X0]
  have l27 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [l26 X0 X1 sK3 sK0]
    conv => enter [1]; rw [← l21 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) sK3 sK0 X1]
  have l28 : ∀ sK3 sK0 X0 X1 : G, (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l25 sK3 sK3 sK0 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l27 X0 X1 sK3 sK0]
  have l29 : ∀ sK3 sK0 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK3) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK0
    conv => enter [1]; rw [l3 sK3 sK0 sK3]
    conv => enter [1]; rw [← l28 sK3 sK0 sK3 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 sK3 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK3 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK3
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l28 sK3 sK0 sK0 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK0]
    conv => enter [1]; rw [l28 sK0 sK0 sK1 (sK1 ◇ sK2)]
  have l32 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ (sK0 ◇ sK0)) ◇ sK3) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK3 sK0]
    conv => enter [1]; rw [l28 sK3 sK0 sK1 (sK1 ◇ sK2)]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l28 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l28 sK1 sK0 sK0 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l35 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h43 sK3 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l32 sK3 sK0 sK1 sK2]
  have l36 : ∀ sK3 sK0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK3 sK0
    conv => enter [1]; rw [l35 sK3 sK0 sK3 sK3]
    conv => enter [1]; rw [← l34 sK0 sK3 sK3]
  have l37 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← l36 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l37 x y z w]

theorem Equation43_4512_53915_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53915 : Equation53915 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53915 X0 X1 sK0 sK0]
    conv => enter [1]; rw [h53915 X1 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l0 X1 X1 X0]
    conv => enter [1]; rw [h53915 X1 X0 sK0 sK0]
  have l5 : ∀ X0 X2 X3 sK0 : G, (X0 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X2 X3 sK0
    conv => enter [1]; rw [← h53915 X0 X0 X2 X3]
    conv => enter [1]; rw [h53915 X0 X0 sK0 sK0]
  have l6 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [h53915 X1 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53915 sK0 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h53915 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l6 X1 X0 X2 sK0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK0)) X2]
  have l11 : ∀ sK0 X0 X2 X3 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 X0 X2 X3
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l5 X0 X2 X3 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l4 X0 X1 sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 X0 X0]
  have l15 : ∀ X1 X0 X2 sK0 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X2))) := by
    intro X1 X0 X2 sK0
    conv => enter [1]; rw [l10 X1 X0 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X2]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l13 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l18 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l11 sK0 X0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [← l15 X1 X0 X2 sK0]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l18 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 (X0 ◇ sK0) sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation43_4512_53915_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53915 : Equation53915 G) : Equation53864 G := by
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
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK2 X0]
  have l6 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ sK2)]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l10 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK1]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l10 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l15 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l11 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l12 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l6 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK2)]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l20 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ sK2)]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK2]
  have l24 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((X2 ◇ X0) ◇ ((X2 ◇ X0) ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1, 2]; rw [← l1 X1 X2 X0]
    conv => enter [1]; rw [h53915 X1 (X2 ◇ X0) sK0 sK1]
  have l25 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53915 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h53915 X1 (sK0 ◇ sK1) sK0 sK1]
  have l26 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← l1 X1 X1 X0]
    conv => enter [1]; rw [h53915 X1 X0 sK0 sK1]
  have l27 : ∀ X0 X2 X3 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X2 X3 sK0 sK1
    conv => enter [1]; rw [← h53915 X0 X0 X2 X3]
    conv => enter [1]; rw [h53915 X0 X0 sK0 sK1]
  have l28 : ∀ X2 X0 X1 sK0 sK1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X1 ◇ (sK0 ◇ sK1)) ◇ X2)) := by
    intro X2 X0 X1 sK0 sK1
    conv => enter [1, 2]; rw [h53915 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (sK0 ◇ sK1)) X2]
  have l29 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [h53915 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [h53915 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
  have l31 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1, 2]; rw [h53915 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK2 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l31 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l1 (sK1 ◇ sK2) sK2 (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l30 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ sK2)) sK2 (sK0 ◇ sK1)]
  have l34 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l29 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK2 (sK0 ◇ sK1)]
  have l35 : ∀ X2 X0 X1 sK0 sK1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X2))) := by
    intro X2 X0 X1 sK0 sK1
    conv => enter [1]; rw [l28 X2 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK1) X2]
  have l36 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l25 X0 X1 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ sK1)]
  have l37 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK1) ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [l24 X1 X0 X2 sK0 sK1]
    conv => enter [1]; rw [l1 (X2 ◇ X0) (X2 ◇ X0) (sK0 ◇ sK1)]
  have l38 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (X0 ◇ (X0 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l32 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l16 sK0 sK1 sK2 sK2]
  have l39 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l33 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l14 sK0 sK1 sK2 sK2]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l20 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l34 sK0 sK1 X0 sK2]
  have l41 : ∀ X1 sK0 sK1 X2 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ sK1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 sK0 sK1 X2 X0
    conv => enter [1]; rw [l27 X1 sK0 sK1 (sK0 ◇ sK1) X2]
    conv => enter [1]; rw [← l35 X2 X0 X1 sK0 sK1]
  have l42 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l36 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l43 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [l37 X1 X0 X2 sK0 sK1]
    conv => enter [1]; rw [l26 (sK0 ◇ sK1) (X2 ◇ X0) sK0 sK1]
  have l44 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (X0 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l38 sK1 X0 sK2 sK0]
  have l45 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l39 sK0 sK1 X0 sK2]
  have l46 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l40 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK2 X0 X0]
  have l47 : ∀ X1 X0 X2 sK1 sK0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X0 X2 sK1 sK0
    conv => enter [1]; rw [l43 X1 X0 X2 sK0 sK1]
    conv => enter [1]; rw [l42 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 sK0]
  have l48 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l41 sK2 sK0 sK1 sK1 sK1]
  have l49 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l41 sK2 sK0 sK1 (sK0 ◇ sK1) sK1]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l41 sK2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l51 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK2 (sK0 ◇ sK1)]
  have l52 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK2 (sK0 ◇ sK1)]
  have l53 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 sK2 (sK0 ◇ sK1)]
  have l54 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK0]
    conv => enter [1]; rw [l26 (sK0 ◇ sK1) sK2 sK0 sK1]
  have l55 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l52 sK1 sK2 sK0]
    conv => enter [1]; rw [l26 (sK0 ◇ sK1) sK2 sK0 sK1]
  have l56 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 (sK0 ◇ sK1) sK2 sK0 sK1]
  have l57 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
    conv => enter [1]; rw [l42 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 sK0]
  have l58 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l55 sK1 sK2 sK0]
    conv => enter [1]; rw [l42 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 sK0]
  have l59 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
    conv => enter [1]; rw [l42 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 sK0]
  have l60 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l58 sK1 sK2 sK0]
    conv => enter [1]; rw [← l57 sK1 sK2 sK0]
  have l61 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l59 sK0 sK1 sK2]
    conv => enter [1]; rw [← l57 sK1 sK2 sK0]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [l60 sK1 sK2 sK0]
  have l63 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l62 sK0 sK1 sK2]
  have l64 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [l61 sK0 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [l64 sK0 sK1 sK2]
  have l66 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [← l42 (sK0 ◇ (sK1 ◇ sK2)) X0 sK1 sK0]
    conv => enter [1]; rw [l65 sK0 sK1 sK2 X0]
  have l67 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1]; rw [l66 sK1 sK0 X0 sK2]
  have l68 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [← h53915 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [h53915 sK0 sK0 X1 X2]
  have l69 : ∀ X0 sK0 X1 X2 sK1 : G, ((X0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (X1 ◇ X2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 X1 X2 sK1
    conv => enter [1]; rw [← h53915 X0 (X0 ◇ sK0) X1 X2]
    conv => enter [1, 2]; rw [h53915 X0 sK0 sK0 sK1]
  have l70 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = ((X0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [← h53915 X0 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ sK0) X1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h53915 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [← l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l70 sK0 sK1 X1 X0]
    conv => enter [1]; rw [← l1 X0 X1 (X0 ◇ sK0)]
  have l74 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l42 (X0 ◇ sK0) (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [l69 X0 sK0 sK1 sK1 sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l42 sK0 (sK0 ◇ sK0) sK1 sK0]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l72 sK0 sK1]
  have l77 : ∀ sK1 sK0 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [← l47 sK1 X1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l73 sK0 sK1 X1 sK1]
  have l78 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1]; rw [l74 sK1 sK0 X0]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l80 : ∀ sK1 sK0 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l77 sK1 sK0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l81 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← l78 sK1 sK2 sK0 sK0]
  have l82 : ∀ sK1 sK2 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1]; rw [l80 sK1 sK0 X1]
  have l83 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l81 sK1 sK0 sK1]
    conv => enter [1]; rw [l82 sK1 sK1 sK0 X1]
  have l84 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53915 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 X0]
    conv => enter [1, 2]; rw [← l46 sK0 sK1 sK2 X0]
  have l85 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l46 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 X0 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l86 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l61 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK0 sK1 sK2 X0]
  have l87 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l84 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l88 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l81 sK1 sK0 sK2]
    conv => enter [1]; rw [l86 sK1 sK2 sK0 X0]
  have l89 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l26 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK1]
    conv => enter [1]; rw [← l87 X0 sK0 sK1 sK2]
  have l90 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l88 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l89 sK0 sK1 sK2 sK1]
  have l91 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l90 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK1)]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l91 sK1 sK0 sK1]
    conv => enter [1]; rw [l26 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) sK0 sK1]
  have l93 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l92 sK1 sK0]
    conv => enter [1]; rw [l42 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1 sK0]
  have l94 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l93 sK1 sK0]
    conv => enter [1]; rw [← l75 sK0 sK1]
  have l95 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [h53915 X0 X1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l78 sK1 sK2 sK0 X1]
  have l96 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l95 X0 X1 sK1 sK2 sK0]
    conv => enter [1]; rw [← l67 sK1 sK2 sK0 X1]
  have l97 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l96 X0 X1 sK1 X0 sK0]
    conv => enter [1]; rw [← l81 sK1 sK0 X0]
  have l98 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l97 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l94 sK1 sK0]
  have l99 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l83 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l100 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l94 sK1 sK0]
    conv => enter [1]; rw [l99 sK1 sK0 X0]
  have l101 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53915 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l98 sK0 sK0 sK0 sK1]
  have l102 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l101 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l103 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l102 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l1 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l104 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l103 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l100 sK0 sK1 X0]
  have l105 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l101 sK0 sK1 sK2]
    conv => enter [1]; rw [← l104 sK0 sK1 sK2 X0]
  have l106 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l105 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l107 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l105 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← l1 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l108 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53915 X0 X1 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l107 sK0 sK1 sK2 X1 X0]
  have l109 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l108 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l106 sK0 sK1 sK2 X1]
  intro x y z
  conv => enter [1]; rw [l109 x y x y z]

theorem Equation43_4512_53915_implies_Equation53867 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h53915 : Equation53915 G) : Equation53867 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53915 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h53915 X1 (sK0 ◇ sK1) sK0 sK1]
  have l2 : ∀ X0 X2 X3 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X2 ◇ X3))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X2 X3 sK0 sK1
    conv => enter [1]; rw [← h53915 X0 X0 X2 X3]
    conv => enter [1]; rw [h53915 X0 X0 sK0 sK1]
  have l3 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ (sK0 ◇ sK1))) ◇ X2) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [h53915 X1 X0 sK0 sK1]
  have l4 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h53915 sK2 X0 sK0 sK1]
  have l5 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X2)) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [l3 X1 X0 X2 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK1)) X2]
  have l6 : ∀ sK2 X0 X2 X3 : G, ((sK2 ◇ sK2) ◇ X0) = (X0 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK2 X0 X2 X3
    conv => enter [1]; rw [l4 sK2 X0 sK2 sK2]
    conv => enter [1]; rw [l2 X0 sK2 sK2 X2 X3]
  have l7 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l4 sK2 (sK0 ◇ sK1) sK0 sK1]
  have l8 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X2))) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [l5 X1 X0 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X2]
  have l9 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l7 X0 X1 sK2 sK0 sK1]
    conv => enter [1]; rw [h43 (sK2 ◇ sK2) (sK0 ◇ sK1)]
  have l10 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [l6 sK2 X0 (sK2 ◇ sK2) X2]
    conv => enter [1]; rw [← l8 X1 X0 X2 sK2 sK2]
  have l11 : ∀ sK2 X0 X1 X2 : G, ((sK2 ◇ sK2) ◇ X0) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK2 X0 X1 X2
    conv => enter [1]; rw [l10 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ sK2 X0 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l11 sK2 X0 sK2 sK2]
    conv => enter [1]; rw [l9 sK2 (X0 ◇ sK2) sK0 sK1 sK2]
  have l13 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l12 sK2 X0 sK0 sK1]
  have l14 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l13 X0 sK2 X0 X0]
    conv => enter [1]; rw [← l13 X1 sK2 X0 X0]
  have l15 : ∀ X0 X1 sK2 X2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = (X2 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l14 (X0 ◇ X1) sK2 X2]
  have l16 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 sK2 sK0]
  have l17 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l16 sK0 sK2 X0 sK0]
  have l18 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l0 X1 X0 X1]
    conv => enter [1]; rw [h53915 X1 X0 sK0 (sK0 ◇ sK1)]
  have l19 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l9 X0 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 X1 X0 sK0 sK1]
  have l20 : ∀ sK0 sK2 X1 X0 : G, (sK0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [l14 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l19 sK0 sK0 sK2 X1 X0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l20 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l21 x y z]
  conv => enter [1]; rw [l17 x z x]

end CommutativeSemigroup5
