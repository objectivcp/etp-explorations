import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

theorem Equation43_4276_4512_4695_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation4696 G := by
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
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2]; rw [l7 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1 X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4276 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l10 sK0 sK1]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l17 X0 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l19 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l14 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l14 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l28 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X1]
  have l29 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l28 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l30 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l29 sK0 sK1 X0 X1]
  have l31 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X2 X3]
  have l32 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK1) X1]
  have l33 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X1]
  have l34 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l35 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l33 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l36 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l32 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ sK1)]
  have l37 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l31 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l38 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l35 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l26 sK0 sK1 X1 X0]
  have l39 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ sK1) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l36 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l5 sK0 sK1 X1 X0]
  have l40 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l37 X0 X1 X2 X3]
  have l41 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l38 sK0 sK1 X0 X1]
  have l42 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l39 sK0 sK1 X0 X1]
  have l43 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l40 X0 X1 X2 X3]
  have l44 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 (X0 ◇ X1) X2]
  have l45 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← l1 X2 X3 (X0 ◇ X1)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4695 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2, 2]; rw [l23 sK0 sK1]
  have l47 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← h4695 X1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4695 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4695 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK1))]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK0 ◇ sK1)]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))))]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK1))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l20 sK1 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1, 2]; rw [l43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1, 2]; rw [l43 sK1 sK1 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1, 2]; rw [l41 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l43 sK1 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1, 2]; rw [l43 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l1 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l44 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l13 sK0 sK1 sK1]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l47 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l72 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2]; rw [l69 sK0 sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1, 2]; rw [l73 sK0 sK1]
  have l75 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [l34 X2 X0 X1]
  have l76 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l34 X0 X1 X2]
    conv => enter [1]; rw [l0 X1 (X0 ◇ X2) X3]
  have l77 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l76 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l78 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l77 X0 X1 X2 X3]
  have l79 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l78 X0 X1 X2 X3]
  have l80 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l47 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l81 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1, 2]; rw [l79 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l82 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l83 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l84 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [l75 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l85 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l86 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l85 sK0 sK1]
    conv => enter [1]; rw [l20 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) sK0 sK1]
  have l87 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1, 2]; rw [← l72 sK0 sK1]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4695 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l87 sK0 sK1]
  have l89 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = sK0 := by
    intro X0 sK0
    conv => enter [1]; rw [h4276 X0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l87 sK0 X0]
  have l90 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [l45 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l90 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l92 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l75 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l93 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l92 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l93 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l95 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [l1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l95 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l70 sK0 sK1]
  have l97 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l89 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l96 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l97 x y]
  conv => enter [1]; rw [l74 x y]

theorem Equation43_4276_4284_4512_implies_Equation53811 (G : Type*) [Magma G] (h43 : Equation43 G) (h4276 : Equation4276 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation53811 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← h4284 X1 X0]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4284 X0 X1]
    conv => enter [1]; rw [h4284 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [h4276 X1 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1, 2]; rw [h43 X0 sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [h4276 sK0 X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4284 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l13 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ X0) X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l15 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l16 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l15 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l16 X0 X1 X2]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l18 X0 X1 X2]
  have l20 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 (sK0 ◇ X0) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4284 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [l14 (sK0 ◇ X0) (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l26 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ X0)]
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ X0) (sK0 ◇ sK0)]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l25 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 X0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1, 2]; rw [← l14 sK0 X0 (sK0 ◇ sK0)]
  have l31 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l17 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4284 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l31 sK0]
  have l34 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l32 X0 sK0]
    conv => enter [1]; rw [← l28 sK0 X0]
  have l35 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [← l33 sK0]
    conv => enter [1]; rw [← l28 sK0 sK0]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [l34 X0 sK0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l35 sK0]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l37 sK0]
    conv => enter [1]; rw [← h4284 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4276 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l37 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l39 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l36 X0 sK0]
    conv => enter [1]; rw [l38 X0 sK0]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l44 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [← l41 sK0 sK0]
  have l45 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l46 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK1 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l47 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4284 sK2 X0]
  have l48 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4284 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l49 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK2 X0]
    conv => enter [1]; rw [← l19 sK1 sK2 X0]
  have l50 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l48 sK1 sK2]
    conv => enter [1]; rw [h43 sK1 (sK1 ◇ sK2)]
  have l51 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l49 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l52 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK2) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l51 sK1 sK2 X0]
    conv => enter [1]; rw [← l14 (sK1 ◇ sK2) X0 sK1]
  have l53 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l46 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l50 sK1 sK2]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l53 sK1 sK2]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK2)]
  have l55 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l54 sK1 sK2]
    conv => enter [1]; rw [l14 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l56 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l55 sK1 sK2]
    conv => enter [1]; rw [l14 (sK1 ◇ sK2) sK1 (sK1 ◇ sK2)]
  have l57 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l56 sK1 sK2]
    conv => enter [1]; rw [← l52 sK1 sK2 (sK1 ◇ sK2)]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4276 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l57 sK1 sK2]
  have l59 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l58 sK0 sK1 sK2]
  have l60 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l59 sK0 sK1 sK2]
  have l61 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l60 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l61 x y z]

theorem Equation43_4270_4512_53807_implies_Equation4268 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation4268 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4270 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ (sK0 ◇ sK1)) sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l4 sK0 sK0 (sK0 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53807 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ X0) sK0 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h53807 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [h43 (X0 ◇ X0) (sK0 ◇ sK0)]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (((X0 ◇ X0) ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← l2 ((X0 ◇ X0) ◇ X1) sK0 X0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK0) X0 sK0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 sK0]
    conv => enter [1]; rw [h43 ((X0 ◇ X0) ◇ X1) (sK0 ◇ sK0)]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK0 sK0]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1]; rw [← h53807 sK0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1, 2]; rw [l2 X1 sK0 X0]
    conv => enter [1]; rw [l21 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l2 X1 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l2 X0 sK0 X0]
  have l25 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l4 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l23 X0 X1 sK0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation43_4270_4512_53807_implies_Equation53864 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation53864 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l6 X0 X2 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l7 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4270 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X0)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l10 sK0 sK1 X0]
    conv => enter [1]; rw [l8 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK1) sK0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h53807 X0]
    conv => enter [1, 2]; rw [h4270 X0 X1]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4270 X2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 (X0 ◇ X0) X0 X1]
  have l16 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l15 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ X1)]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l16 X2 X0 X1]
    conv => enter [1, 2]; rw [← l14 X0 X1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l13 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) X0]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 X0 (sK0 ◇ sK1)]
  have l20 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l3 (X0 ◇ X1) X2 X3]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l20 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l22 X0 X1 X2 X3]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (((sK0 ◇ sK1) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [← l2 X0 (sK0 ◇ sK1)]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [l23 ((sK0 ◇ sK1) ◇ X0) X0 X0 X0]
  have l26 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l17 X0 ((sK0 ◇ sK1) ◇ X0) X0]
    conv => enter [1]; rw [← l25 sK0 sK1 X0]
  have l27 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 X0]
    conv => enter [1]; rw [l26 X0 sK0 sK1]
  have l28 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1]; rw [l5 X1 X0 X0]
  have l29 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l27 X1 sK0 sK0 sK1]
    conv => enter [1]; rw [l28 X1 sK0 X0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK0 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l29 sK0 sK1 sK0 (sK1 ◇ sK2)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l30 sK0 sK1]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y z]

theorem Equation43_4270_4512_41529_implies_Equation308 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation308 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4270 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l3 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l12 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l9 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l13 : ∀ X0 sK0 X2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l12 X0 sK0 X2 X0]
    conv => enter [1, 2]; rw [← l2 X2 sK0 X0]
  have l14 : ∀ X0 sK0 X2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X0 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l13 X0 sK0 X2]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l16 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [l2 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0)]
  have l17 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l16 sK0 X0 sK1]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l15 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l20 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l19 sK0 sK1 X0 X1]
  have l21 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ (X0 ◇ X0)) sK0 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41529 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l22 X0 sK0]
    conv => enter [1]; rw [h43 (X0 ◇ (X0 ◇ X0)) (sK0 ◇ sK0)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) sK1]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l25 X0 sK0]
    conv => enter [1, 2]; rw [h4270 X0 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l27 X0 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1 (sK0 ◇ sK0) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK0) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l21 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4270 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l38 x y]

theorem Equation43_4270_4512_41529_implies_Equation41530 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation41530 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← h4270 X0 sK0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l4 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 (sK0 ◇ sK1) sK0 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0 sK0]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 sK0 X2 X1
    conv => enter [1, 1]; rw [l3 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l16 : ∀ X0 sK0 X2 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 X2 X1
    conv => enter [1]; rw [l12 X0 sK0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l17 : ∀ X0 sK0 X2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [l16 X0 sK0 X2 X0]
    conv => enter [1, 2]; rw [← l2 X2 sK0 X0]
  have l18 : ∀ X0 sK0 X2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X2)) = (X0 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l17 X0 sK0 X2]
  have l19 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [l2 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0)]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l19 sK0 X0 sK1]
    conv => enter [1]; rw [← l14 (sK0 ◇ sK1) X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41529 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ (X0 ◇ X0)) sK0 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41529 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l14 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1]; rw [h43 (X0 ◇ (X0 ◇ X0)) (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) sK1]
  have l26 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l24 X0 sK0]
    conv => enter [1, 2]; rw [h4270 X0 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l26 X0 sK0]
    conv => enter [1]; rw [← l4 X0 sK0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4270 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l36 x y]
  conv => enter [1]; rw [l11 x y]

theorem Equation43_4270_4512_4695_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l3 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l5 X0 X2 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l1 X1 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l10 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X0 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2 X3]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4270 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l11 X2 X0 X1]
  have l18 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = ((X0 ◇ X2) ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 (X0 ◇ X2) X3]
  have l19 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ X2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l9 X1 (X0 ◇ X2)]
    conv => enter [1, 2]; rw [l11 X1 X0 X2]
  have l20 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l19 X1 X0 X2]
    conv => enter [1]; rw [← l14 X0 X1 (X0 ◇ X2) X2]
  have l21 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X2 (X1 ◇ X3)]
  have l22 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l20 X1 X0 X2]
    conv => enter [1, 2]; rw [l17 X1 (X0 ◇ X2) X2]
  have l23 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l21 X0 X1 X2 X3]
  have l24 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l23 X0 X1 X2 X3]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4695 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h4695 X1]
  have l27 : ∀ X1 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    intro X1
    conv => enter [1, 2]; rw [l16 X1 X1]
    conv => enter [1]; rw [l26 X1 X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))]
  have l29 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1, 2]; rw [l7 X1 (X0 ◇ X1) ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l30 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l29 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l24 X1 (X0 ◇ X1) X0 (X1 ◇ (X0 ◇ X1))]
  have l31 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l22 X0 X1 (X0 ◇ X1)]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l16 X0 X1]
    conv => enter [1]; rw [← l31 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l32 X0 X1]
    conv => enter [1]; rw [l27 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l33 X0 (X1 ◇ X0)]
  have l35 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l33 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l34 X0 X1]
  intro x y
  conv => enter [1]; rw [l35 x y]

theorem Equation43_4268_4270_4284_4512_54318_implies_Equation4271 (G : Type*) [Magma G] (h43 : Equation43 G) (h4268 : Equation4268 G) (h4270 : Equation4270 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h54318 : Equation54318 G) : Equation4271 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4268 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l2 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((X1 ◇ X1) ◇ X0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0 X1]
    conv => enter [1]; rw [h43 X0 (X1 ◇ X1)]
  have l3 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [← l2 X0 sK0 X1]
  have l4 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l1 X1 X0 sK0]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X0) sK0]
    conv => enter [1, 2]; rw [l3 X1 X0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4268 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l7 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l5 X1 sK0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 X1]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 X1]
    conv => enter [1]; rw [l7 X1 sK0]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4284 X2 (X0 ◇ X1)]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54318 X2 X0 X1]
    conv => enter [1]; rw [← l9 X2 X0 X1]
  have l11 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [l10 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l4 X1 X0 sK0]
  have l12 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [l11 X2 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 X1]
  have l13 : ∀ X2 X0 X1 sK0 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 sK0
    conv => enter [1]; rw [l12 X2 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 X0]
  have l14 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ X1)) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l8 sK0 X2]
    conv => enter [1]; rw [← l13 X2 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x x y z]

theorem Equation43_4268_4270_4276_4284_4512_53978_54318_implies_Equation54340 (G : Type*) [Magma G] (h43 : Equation43 G) (h4268 : Equation4268 G) (h4270 : Equation4270 G) (h4276 : Equation4276 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53978 : Equation53978 G) (h54318 : Equation54318 G) : Equation54340 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X3 ◇ (X3 ◇ X0)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h54318 X1 X1 X2]
    conv => enter [1]; rw [← h53978 X3 X0 X1 X2]
  have l1 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4268 sK1 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4268 sK1 X0]
  have l2 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4268 sK2 sK3]
    conv => enter [1]; rw [h4268 sK2 X0]
  have l3 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (sK3 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← h4268 sK3 sK0]
    conv => enter [1]; rw [h4268 sK3 X0]
  have l4 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l3 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l5 : ∀ sK3 sK0 X0 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK0 sK3]
    conv => enter [1]; rw [h4270 sK3 X0]
  have l6 : ∀ sK3 sK2 X0 : G, (sK3 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (X0 ◇ X0)) := by
    intro sK3 sK2 X0
    conv => enter [1]; rw [← l4 sK3 sK3 sK2]
    conv => enter [1]; rw [l5 sK3 sK3 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4276 X0 X1]
    conv => enter [1]; rw [h4270 X1 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h4276 X0 X1]
    conv => enter [1]; rw [h4268 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4276 X1 X0]
  have l9 : ∀ X0 sK3 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK3 sK2
    conv => enter [1]; rw [h4276 X0 sK3]
    conv => enter [1]; rw [← l6 sK3 sK2 sK3]
  have l10 : ∀ sK3 sK2 X1 : G, (sK3 ◇ (sK2 ◇ sK3)) = (X1 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK3 sK2 X1
    conv => enter [1]; rw [← l9 sK3 sK3 sK2]
    conv => enter [1]; rw [l8 sK3 X1]
    conv => enter [1, 2]; rw [l9 sK3 sK3 sK2]
  have l11 : ∀ X1 X2 sK3 sK2 : G, (X1 ◇ (X2 ◇ X2)) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro X1 X2 sK3 sK2
    conv => enter [1]; rw [← l7 X1 X1 X2]
    conv => enter [1]; rw [l9 X1 sK3 sK2]
  have l12 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK3 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l10 sK3 sK2 sK1]
  have l13 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK3 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3
    conv => enter [1]; rw [l2 sK2 sK3 (sK3 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l10 sK3 sK2 sK2]
  have l14 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [l13 sK2 sK3]
    conv => enter [1]; rw [← l10 sK3 sK2 sK2]
  have l15 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l12 sK1 sK2 sK3]
    conv => enter [1]; rw [← l10 sK3 sK2 sK1]
  have l16 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l15 sK1 sK2 sK3]
    conv => enter [1]; rw [← l14 sK2 sK3]
  have l17 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l15 sK1 sK2 sK3]
    conv => enter [1]; rw [l10 sK3 sK2 X0]
    conv => enter [1, 2]; rw [← l15 sK1 sK2 sK3]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [h4284 X1 X0]
  have l19 : ∀ X1 X0 sK3 sK2 : G, (X1 ◇ (X0 ◇ X1)) = (sK3 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK3 sK2
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [l11 X1 X0 sK3 sK2]
  have l20 : ∀ X1 X0 sK2 sK3 : G, (X1 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK2 sK3
    conv => enter [1]; rw [l19 X1 X0 sK3 sK2]
    conv => enter [1]; rw [← l14 sK2 sK3]
  have l21 : ∀ X1 X0 sK1 sK2 sK3 : G, (X1 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 sK1 sK2 sK3
    conv => enter [1]; rw [l20 X1 X0 sK2 sK3]
    conv => enter [1]; rw [← l16 sK1 sK2 sK3]
  have l22 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4284 X2 (X0 ◇ X1)]
  have l23 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54318 X2 X0 X1]
    conv => enter [1]; rw [← l22 X2 X0 X1]
  have l24 : ∀ X2 X0 X1 sK1 sK2 sK3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))))) := by
    intro X2 X0 X1 sK1 sK2 sK3
    conv => enter [1]; rw [l23 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l21 X1 X0 sK1 sK2 sK3]
  have l25 : ∀ X2 X0 X1 sK1 sK2 sK3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3)))) := by
    intro X2 X0 X1 sK1 sK2 sK3
    conv => enter [1]; rw [l24 X2 X0 X1 sK1 sK2 sK3]
    conv => enter [1, 2]; rw [← l17 sK1 sK2 sK3 X0]
  have l26 : ∀ sK1 sK2 sK3 X2 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X2 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 sK3 X2]
    conv => enter [1]; rw [← l25 X2 X0 X1 sK1 sK2 sK3]
  have l27 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1, 2]; rw [h43 (sK2 ◇ sK3) X0]
  have l28 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK1 X0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l27 sK1 sK2 sK3 X0]
  have l29 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l28 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK1 ◇ (sK2 ◇ sK3)) X0]
  have l30 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← l29 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [l29 sK1 sK2 sK3 X1]
  have l31 : ∀ sK2 sK3 X0 : G, ((sK2 ◇ sK3) ◇ X0) = (sK2 ◇ (X0 ◇ sK3)) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK2 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l32 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ X0) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK2 X0 sK3]
    conv => enter [1]; rw [← l31 sK2 sK3 X0]
  have l33 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK3 sK0]
    conv => enter [1]; rw [← l32 sK1 sK2 sK3 sK0]
  have l34 : ∀ sK2 sK3 sK0 X0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [l33 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK1 sK2 sK3 X0]
  have l35 : ∀ X0 X1 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l33 sK2 sK3 sK0 sK1]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l35 sK1 sK1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l26 sK1 sK2 sK3 sK1 sK1 sK1]
  have l37 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l34 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK3 sK0]
  have l38 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l32 sK1 sK2 sK3 X0]
    conv => enter [1]; rw [h43 (sK2 ◇ sK3) X0]
  have l39 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l34 sK2 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [l38 sK2 sK2 sK3 X0]
  intro x y z w
  conv => enter [1]; rw [← l39 y z w x]
  conv => enter [1]; rw [l37 y z w x]

theorem Equation43_4268_4270_4276_53858_implies_Equation53878 (G : Type*) [Magma G] (h43 : Equation43 G) (h4268 : Equation4268 G) (h4270 : Equation4270 G) (h4276 : Equation4276 G) (h53858 : Equation53858 G) : Equation53878 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4268 sK1 sK2]
    conv => enter [1]; rw [h4268 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4268 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4268 sK2 X0]
  have l3 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK2 X0]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 sK1]
    conv => enter [1]; rw [h4270 sK1 X0]
  have l5 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [h4270 sK2 X0]
  have l6 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l3 sK2 sK2 sK2 sK1]
    conv => enter [1]; rw [l5 sK2 sK2 sK2 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4276 X0 X1]
    conv => enter [1]; rw [h4270 X1 X2]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h4276 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK2 sK1]
  have l9 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h4276 X0 sK2]
    conv => enter [1]; rw [← l6 sK2 sK1 sK2]
  have l10 : ∀ X1 X2 sK2 sK1 : G, (X1 ◇ (X2 ◇ X2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK2 sK1
    conv => enter [1]; rw [← l7 X1 X1 X2]
    conv => enter [1]; rw [l9 X1 sK2 sK1]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l8 sK2 sK1 sK2]
    conv => enter [1]; rw [← l6 sK2 sK1 sK2]
  have l12 : ∀ X0 X1 X2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 X2 sK3 sK0
    conv => enter [1]; rw [h53858 X0 X1 X2 sK0 sK3]
    conv => enter [1, 2, 2]; rw [h43 sK0 sK3]
  have l13 : ∀ sK2 sK1 X1 X2 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK1 X1 X2 sK3 sK0
    conv => enter [1]; rw [← l10 sK2 sK2 sK2 sK1]
    conv => enter [1]; rw [l12 sK2 X1 X2 sK3 sK0]
  have l14 : ∀ sK1 sK2 X1 X2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X1 X2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [l13 sK2 sK1 X1 X2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l14 x y x y z w]

@[equational_result]
theorem Equation4271_implies_Equation54340 (G : Type*) [Magma G] (h4271 : Equation4271 G) : Equation54340 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l1 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [← h4271 X0 sK2 sK3]
    conv => enter [1]; rw [h4271 X0 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l0 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation3253_53807_implies_Equation307 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h53807 : Equation53807 G) : Equation307 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1]; rw [← h53807 X0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation3253_53807_implies_Equation41529 (G : Type*) [Magma G] (h3253 : Equation3253 G) (h53807 : Equation53807 G) : Equation41529 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3253 X0]
    conv => enter [1]; rw [← h53807 X0]
  intro x
  conv => enter [1]; rw [l0 x]
  conv => enter [1, 2]; rw [h3253 x]

theorem Equation43_3253_4512_41529_implies_Equation307 (G : Type*) [Magma G] (h43 : Equation43 G) (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation307 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l0 sK0 X0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41529 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l10 x]

theorem Equation43_3253_4512_41529_implies_Equation53860 (G : Type*) [Magma G] (h43 : Equation43 G) (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h41529 : Equation41529 G) : Equation53860 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← h3253 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ sK1) X0]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h41529 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation43_3253_4512_4695_implies_Equation3 (G : Type*) [Magma G] (h43 : Equation43 G) (h3253 : Equation3253 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation3 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3253 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3253 X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4695 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

theorem Equation43_411_4512_53807_implies_Equation3 (G : Type*) [Magma G] (h43 : Equation43 G) (h411 : Equation411 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h53807 X0]
    conv => enter [1]; rw [← h411 X0]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X2 ◇ X1) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [h43 X0 (X2 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← l6 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [l5 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h53807 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l9 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l11 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l10 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l11 x]

theorem Equation43_411_4512_53807_implies_Equation4695 (G : Type*) [Magma G] (h43 : Equation43 G) (h411 : Equation411 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation4695 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h53807 X0]
    conv => enter [1]; rw [← h411 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l3 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53807 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53807 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l13 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [l12 sK0]
  intro x
  conv => enter [1]; rw [l13 x]
  conv => enter [1, 2, 2]; rw [← l0 x]

theorem Equation411_41529_implies_Equation3 (G : Type*) [Magma G] (h411 : Equation411 G) (h41529 : Equation41529 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h411 sK0]
    conv => enter [1]; rw [← h41529 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation411_4695_implies_Equation3 (G : Type*) [Magma G] (h411 : Equation411 G) (h4695 : Equation4695 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h411 X0]
    conv => enter [1]; rw [← h4695 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation307_implies_Equation41529 (G : Type*) [Magma G] (h307 : Equation307 G) : Equation41529 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h307 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation43_41733_53860_implies_Equation323 (G : Type*) [Magma G] (h43 : Equation43 G) (h41733 : Equation41733 G) (h53860 : Equation53860 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41733 X0 X1]
    conv => enter [1, 2, 2]; rw [h53860 X0 X1]
    conv => enter [1, 2]; rw [← h41733 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41733 sK0 sK1]
    conv => enter [1, 2]; rw [← h53860 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_307_4512_41733_53860_implies_Equation41736 (G : Type*) [Magma G] (h43 : Equation43 G) (h307 : Equation307 G) (h4512 : Equation4512 G) (h41733 : Equation41733 G) (h53860 : Equation53860 G) : Equation41736 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h307 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 X0 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h43 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h307 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53860 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ X0))]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = (sK1 ◇ ((sK1 ◇ X0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0) (sK0 ◇ sK1)]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ X0)]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 X0 (sK0 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l19 sK0 sK1 X0]
  have l21 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [l21 sK1 X0 sK0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h41733 X0 X1]
    conv => enter [1, 2, 2]; rw [h53860 X0 X1]
    conv => enter [1, 2]; rw [← h41733 X0 X1]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h41733 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ X0)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ (sK1 ◇ X0)) (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41733 sK0 sK1]
    conv => enter [1, 2]; rw [← h53860 sK0 sK1]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ (sK1 ◇ X0))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1, 2]; rw [← l23 sK0 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ X0) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0) (sK0 ◇ (sK1 ◇ sK1))]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK1 ◇ X0)]
  have l31 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← l0 sK1 X0 (sK0 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1 X0]
    conv => enter [1]; rw [← l22 sK0 sK1 X0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l32 sK0 sK1 X0]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l35 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l36 x y]
  conv => enter [1]; rw [l15 x y]

theorem Equation323_4284_implies_Equation41736 (G : Type*) [Magma G] (h323 : Equation323 G) (h4284 : Equation4284 G) : Equation41736 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h323 sK0 (sK1 ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h323 X0 sK1]
    conv => enter [1]; rw [h4284 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [l0 x y]

theorem Equation43_47_4512_implies_Equation41733 (G : Type*) [Magma G] (h43 : Equation43 G) (h47 : Equation47 G) (h4512 : Equation4512 G) : Equation41733 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h47 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [h43 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 (sK0 ◇ sK1) sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h43 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h47 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation308_53878_implies_Equation3267 (G : Type*) [Magma G] (h308 : Equation308 G) (h53878 : Equation53878 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [h308 x y]
  conv => enter [1]; rw [h53878 x y z w]

theorem Equation40_43_308_4512_54009_implies_Equation41580 (G : Type*) [Magma G] (h40 : Equation40 G) (h43 : Equation43 G) (h308 : Equation308 G) (h4512 : Equation4512 G) (h54009 : Equation54009 G) : Equation41580 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h308 X1 X0]
    conv => enter [1, 2]; rw [h43 X1 X0]
  have l1 : ∀ sK2 X1 X0 : G, (sK2 ◇ sK2) = (X1 ◇ (X0 ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h40 sK2 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ sK2) := by
    intro X0 X1 sK2
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [← l1 sK2 X0 X1]
  have l3 : ∀ sK4 sK1 sK0 X0 : G, ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK4 ◇ X0)) := by
    intro sK4 sK1 sK0 X0
    conv => enter [1, 1]; rw [h43 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK4 X0]
  have l4 : ∀ sK3 sK4 sK1 sK0 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK3 ◇ X0)) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1, 1]; rw [h43 sK3 (sK4 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← h4512 (sK4 ◇ (sK1 ◇ sK0)) sK3 X0]
  have l5 : ∀ sK3 sK4 sK1 sK0 X0 : G, ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK3)) := by
    intro sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l4 sK3 sK4 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h43 sK3 X0]
  have l6 : ∀ X0 X1 sK4 sK1 sK0 X2 X3 : G, (X0 ◇ (X0 ◇ X1)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ X3)) := by
    intro X0 X1 sK4 sK1 sK0 X2 X3
    conv => enter [1]; rw [h54009 X0 X1 (sK1 ◇ sK0) sK4 X2 X3]
    conv => enter [1]; rw [← l3 sK4 sK1 sK0 (X2 ◇ X3)]
  have l7 : ∀ sK2 sK4 sK1 sK0 X2 X3 : G, (sK2 ◇ sK2) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X2 ◇ X3)) := by
    intro sK2 sK4 sK1 sK0 X2 X3
    conv => enter [1]; rw [← l2 sK2 sK2 sK2]
    conv => enter [1]; rw [l6 sK2 sK2 sK4 sK1 sK0 X2 X3]
  have l8 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, (sK2 ◇ sK2) = ((sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l7 sK2 sK4 sK1 sK0 X0 sK3]
    conv => enter [1]; rw [← l5 sK3 sK4 sK1 sK0 X0]
  have l9 : ∀ sK2 X0 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l8 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [h43 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))) X0]
  intro x y z w u
  conv => enter [1]; rw [l9 x x y z w u]

theorem Equation40_43_3267_implies_Equation41580 (G : Type*) [Magma G] (h40 : Equation40 G) (h43 : Equation43 G) (h3267 : Equation3267 G) : Equation41580 G := by
  have l0 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h3267 X0 X1 (sK1 ◇ sK0) sK4]
    conv => enter [1, 2, 2]; rw [h43 (sK1 ◇ sK0) sK4]
  have l1 : ∀ sK2 X0 X1 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h40 sK2 X0]
    conv => enter [1]; rw [l0 X0 X1 sK4 sK1 sK0]
  have l2 : ∀ sK2 X1 sK4 sK1 sK0 X0 : G, (sK2 ◇ sK2) = (X1 ◇ ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 X1 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l1 sK2 X1 X0 sK4 sK1 sK0]
    conv => enter [1, 2]; rw [h43 X0 (sK4 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ sK2 X0 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 X0 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l2 sK2 X0 sK4 sK1 sK0 sK3]
    conv => enter [1, 2]; rw [h43 (sK4 ◇ (sK1 ◇ sK0)) sK3]
  intro x y z w u
  conv => enter [1]; rw [l3 x x y z w u]

theorem Equation40_43_308_3267_implies_Equation53878 (G : Type*) [Magma G] (h40 : Equation40 G) (h43 : Equation43 G) (h308 : Equation308 G) (h3267 : Equation3267 G) : Equation53878 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h40 X0 sK1]
    conv => enter [1]; rw [h308 sK1 sK2]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h3267 X0 X1 sK0 sK3]
    conv => enter [1, 2, 2]; rw [h43 sK0 sK3]
  have l2 : ∀ sK1 sK2 X0 X1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 X1 sK3 sK0
    conv => enter [1]; rw [← l0 X0 sK1 sK2]
    conv => enter [1]; rw [l1 X0 X1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y x y z w]

@[equational_result]
theorem Equation38_implies_Equation41805 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation41805 G := by
  have l0 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ sK3) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h38 sK2 (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [h38 sK2 sK3]
  intro x y z w u
  conv => enter [1]; rw [← l0 x y z w u]

theorem Equation3_43_4798_41736_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h43 : Equation43 G) (h4798 : Equation4798 G) (h41736 : Equation41736 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h41736 X1 X1]
    conv => enter [1]; rw [← h4798 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

end CommutativeSemigroup5
