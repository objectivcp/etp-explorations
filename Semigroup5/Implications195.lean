import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_42213_implies_Equation41999 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42213 : Equation42213 G) : Equation41999 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X2 X1 X0 X3 : G, ((X2 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [h42213 (X2 ◇ (X1 ◇ (X2 ◇ X0))) X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h42213 X0 X1 X2]
  have l2 : ∀ X0 sK0 sK2 : G, (X0 ◇ sK0) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ X0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h42213 X0 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (sK2 ◇ X0)]
  have l3 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h42213 X0 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ X0)]
  have l4 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ X0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l3 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ X0)]
  have l5 : ∀ X0 sK0 sK2 : G, (X0 ◇ sK0) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l2 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ X0)]
  have l6 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l1 X2 X1 X0 X3]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ (X2 ◇ X0)) X3]
  have l7 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l6 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l8 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l7 X2 X3 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l9 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l4 (sK2 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l10 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ X0)) = (sK2 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [← l5 X0 sK0 sK2]
  have l11 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (X0 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l4 X0 sK2 sK0]
    conv => enter [1]; rw [l10 sK2 sK0 X0]
  have l12 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l5 (sK2 ◇ (sK2 ◇ sK0)) sK0 sK2]
  have l13 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l12 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) sK0]
  have l14 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 (sK2 ◇ (sK2 ◇ sK0)) sK2 sK0]
    conv => enter [1]; rw [l13 sK2 sK0]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK0 sK2]
    conv => enter [1]; rw [l14 sK2 sK0]
  have l16 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [← l15 sK0 sK2]
  have l17 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 sK2]
  have l18 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [← l16 sK1 sK2 sK0]
  have l19 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h42213 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [l18 sK1 sK2 sK0]
  have l20 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l19 sK2 sK0 X0 sK2]
    conv => enter [1]; rw [← h42213 sK0 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l21 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ X0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l4 X0 sK2 sK0]
    conv => enter [1]; rw [l20 sK2 sK0 (sK2 ◇ X0)]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h42213 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
    conv => enter [1, 2, 2]; rw [l20 sK2 sK0 (sK0 ◇ sK1)]
  have l23 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK0]
    conv => enter [1]; rw [← h42213 sK1 sK0 sK0]
  have l24 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 sK2 sK0 sK1 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l23 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l23 sK1 sK2 sK0]
  have l27 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK2 sK0 sK1]
    conv => enter [1]; rw [l11 sK2 (sK0 ◇ sK1) sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l26 sK1 sK2 sK0]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [l21 sK0 sK2 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l30 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [l27 sK2 sK0 sK1]
  have l31 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l30 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ sK0) X0]
  have l32 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h42213 (sK2 ◇ sK0) X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK2 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (sK2 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l29 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [← l33 sK1 sK2 sK0 X0]
  have l35 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l32 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0 (sK0 ◇ sK1) (sK2 ◇ sK0)]
  have l36 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l35 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l37 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l36 sK2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l31 sK2 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l38 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l37 sK2 sK0 X0 sK2]
    conv => enter [1]; rw [← h42213 X0 (sK2 ◇ sK0) (sK0 ◇ sK2)]
  have l39 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK0 sK1]
    conv => enter [1]; rw [l38 sK2 sK0 sK1]
  have l40 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l39 sK2 sK0 sK1]
    conv => enter [1]; rw [l26 sK1 sK2 sK0]
  have l41 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) = (sK2 ◇ (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h42213 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l40 sK2 sK0 sK1]
  have l42 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h42213 (sK0 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [← l41 sK1 sK2 sK0 X0]
  have l43 : ∀ X1 sK1 sK2 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro X1 sK1 sK2 sK0 X0
    conv => enter [1]; rw [h42213 X1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1, 2, 2]; rw [← l42 sK0 sK1 (X0 ◇ X1) sK2]
  have l44 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [h42213 X1 (sK0 ◇ sK1) X1]
    conv => enter [1]; rw [← l43 X1 sK1 sK2 sK0 X1]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42213 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK1 sK2 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l42 sK0 sK1 sK0 sK0]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l25 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l44 sK0 sK0 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← h42213 sK1 sK0 sK0]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l23 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l50 x y z]

theorem Equation4512_41999_implies_Equation42194 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation42194 G := by
  have l0 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK0 X0]
  have l1 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l2 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41999 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0))) = (X0 ◇ sK0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← h41999 X0 sK0 (sK1 ◇ (sK2 ◇ sK0))]
  have l7 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK1 ◇ (sK2 ◇ sK0)) X1]
  have l8 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41999 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
  have l9 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h41999 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
  have l10 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l7 sK0 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h41999 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l11 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41999 X0 X2 X0]
  have l13 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [← h41999 (sK1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l14 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [← h41999 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ sK2) sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h41999 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK2) = (sK0 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [← l13 sK2 sK0 sK1]
  have l20 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [← l13 sK2 sK0 sK1]
  have l21 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l20 sK1 sK2 sK0 X0]
  have l22 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l21 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ sK0)) sK2 X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41999 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [l14 sK1 sK2 sK0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h41999 (sK1 ◇ sK2) X0 (sK1 ◇ (sK2 ◇ sK0))]
  have l25 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2]
  have l26 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [← l24 sK0 sK1 sK2 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h41999 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0]
  have l27 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l26 sK1 sK2 X1 X1 sK0]
    conv => enter [1]; rw [← h41999 X1 (sK1 ◇ sK2) X1]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h41999 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 sK0]
    conv => enter [1, 2]; rw [← h41999 (sK1 ◇ (sK2 ◇ sK0)) sK0 sK0]
  have l29 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h41999 (sK1 ◇ (sK2 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2, 2]; rw [← l25 sK1 sK2 sK0]
  have l30 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l29 sK1 sK2 sK0 X0]
    conv => enter [1, 2, 2]; rw [l12 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l31 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l30 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← l11 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l31 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [l24 sK0 sK1 sK2 sK0]
  have l33 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l32 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK0]
  have l34 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK0 sK1]
    conv => enter [1]; rw [l33 sK1 sK2 sK0 sK2]
  have l35 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l33 sK1 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK0))]
  have l36 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l27 (sK2 ◇ sK0) sK0 sK1 sK2]
    conv => enter [1]; rw [l34 sK2 sK0 sK1]
  have l37 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l9 sK0 (sK2 ◇ sK0) sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l38 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l37 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [l27 sK2 sK0 sK1 sK2]
  have l39 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l27 (sK2 ◇ sK0) sK0 sK1 sK2]
    conv => enter [1]; rw [l38 sK2 sK0 sK1]
  have l40 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l36 sK2 sK0 sK1]
    conv => enter [1]; rw [l39 sK2 sK0 sK1]
  have l41 : ∀ X0 X1 sK0 sK1 sK2 : G, ((X0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ X1) sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK2 ◇ sK0))]
  have l42 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 1]; rw [← l10 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
  have l43 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l42 X0 sK0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK0)) X1]
  have l44 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l41 X0 X1 sK0 sK1 sK2]
  have l45 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X1))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X1]
    conv => enter [1]; rw [l43 X0 sK0 sK1 sK2 X1]
  have l46 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1) = (X0 ◇ (((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK0) X1]
  have l47 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l46 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK0)) sK0 X1]
  have l48 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l47 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [l35 sK1 sK2 sK0 sK0 X1]
  have l49 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l48 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [l10 sK0 X1 sK1 sK2]
  have l50 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) X0 X1]
    conv => enter [1]; rw [l49 sK0 sK1 sK2 X0 X1]
  have l51 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ sK2) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) X0]
    conv => enter [1, 1]; rw [← l19 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2 X0]
  have l53 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ (((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) ◇ X0)) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [← l50 sK0 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← l52 sK0 sK2 sK1 X0]
  have l54 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ X0))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l53 sK2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) X0]
  have l55 : ∀ sK2 X0 sK0 sK1 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = (sK0 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ X0))) := by
    intro sK2 X0 sK0 sK1
    conv => enter [1]; rw [l54 sK2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l22 sK2 sK0 sK1 X0]
  have l56 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l45 sK2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l55 sK2 X0 sK0 sK1]
  have l57 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [h41999 (sK2 ◇ (sK1 ◇ sK2)) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l40 sK2 sK1 sK0]
  have l58 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l57 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK2 sK0 sK1 sK2]
  have l59 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l58 sK2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK2 sK1 sK2]
  have l60 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l59 sK2 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l27 sK2 sK2 sK1 sK2]
  have l61 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l60 sK2 sK1 X0]
  have l62 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41999 (sK1 ◇ sK2) X0 sK1]
    conv => enter [1, 2]; rw [← h41999 sK2 sK1 sK1]
  have l63 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h41999 sK1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← l62 sK1 sK2 sK2]
  have l64 : ∀ sK1 X0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l63 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l61 sK2 sK1 sK2]
  have l65 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h41999 sK0 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l66 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [l50 sK0 sK1 sK2 sK2 (sK2 ◇ (sK2 ◇ sK0))]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l66 sK0 sK1 sK2]
    conv => enter [1]; rw [← l56 sK2 sK0 sK1 (sK2 ◇ (sK2 ◇ sK0))]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l50 sK0 sK1 sK2 sK2 (sK2 ◇ sK0)]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l70 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l27 sK2 sK0 sK1 sK2]
  have l71 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l64 sK1 sK2 sK2]
    conv => enter [1]; rw [← l70 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l71 x y z]

theorem Equation4512_42194_implies_Equation41999 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42194 : Equation42194 G) : Equation41999 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h42194 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h42194 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
  have l2 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h42194 sK2 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK0 X0]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h42194 sK2 (sK2 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK2 ◇ sK0) X0]
  have l4 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h42194 sK2 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) X0]
  have l5 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h42194 sK0 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 (X0 ◇ sK2)]
  have l6 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h42194 (sK2 ◇ sK0) X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK0) (X0 ◇ sK2)]
  have l7 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1, 2]; rw [h42194 X0 X1 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))))]
  have l8 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l6 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (X0 ◇ sK2)]
  have l9 : ∀ sK0 X0 sK2 : G, (sK0 ◇ X0) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK2)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l5 sK0 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (X0 ◇ sK2)]
  have l10 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l11 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [h42194 X1 X0 (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0))]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK2 sK0 X0]
  have l12 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l4 sK2 sK0 X0]
  have l13 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X1) = (X0 ◇ (X0 ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ X1))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [← l12 X0 sK2 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) X1]
  have l14 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = (X0 ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [l11 X1 X0 sK2 sK0]
    conv => enter [1]; rw [← h4512 X0 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))]
  have l15 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X1) = (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l13 sK2 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 X1]
  have l16 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [l14 X1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 ((X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))]
  have l17 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [l16 X1 X0 sK2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l18 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))))))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [l17 X1 X0 sK2 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l19 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [l18 X1 X0 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← l15 sK2 sK0 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
  have l20 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ sK1) = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1) ◇ (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h42194 X0 sK1 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK2 sK0 sK1]
  have l21 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK1 ◇ (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 1]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1) X0]
  have l22 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ X0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l21 sK2 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1 X0]
  have l23 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l20 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1 (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK1) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))]
  have l24 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l23 X0 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1 (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l25 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l24 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l22 sK2 sK0 (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1]
  have l26 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 sK2 sK0 ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l27 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l26 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l28 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l27 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK0)) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l29 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l28 sK2 sK0]
    conv => enter [1]; rw [← l7 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) sK0]
  have l30 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l29 sK2 sK0]
    conv => enter [1]; rw [← l19 (sK2 ◇ (sK2 ◇ sK0)) sK2 sK2 sK0]
  have l31 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l30 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) sK2]
  have l32 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l30 sK2 sK0]
    conv => enter [1]; rw [← l8 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
  have l33 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 1]; rw [l30 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK0)) sK2 X0]
  have l34 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [← l31 sK2 sK0]
  have l35 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 X0]
    conv => enter [1, 1]; rw [← l31 sK2 sK0]
  have l36 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l35 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
  have l37 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l33 sK2 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l34 sK0 sK2]
  have l38 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l37 sK2 sK0]
    conv => enter [1]; rw [l32 sK2 sK0]
  have l39 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK2 ◇ (sK2 ◇ sK0))]
  have l40 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l39 sK2 sK0]
  have l41 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l3 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l40 sK2 sK0]
  have l42 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ sK0) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l41 sK2 sK0]
    conv => enter [1]; rw [← h42194 (sK2 ◇ sK0) sK2 (sK2 ◇ (sK2 ◇ sK0))]
  have l43 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← l42 sK2 sK0]
  have l44 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK0) sK2]
  have l45 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))]
    conv => enter [1, 2]; rw [← l2 sK2 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l46 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ sK1) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l25 (sK2 ◇ sK0) sK1 sK2 sK0]
    conv => enter [1]; rw [l45 sK1 sK2 sK0]
  have l47 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l44 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) sK2]
  have l48 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK0 sK1]
    conv => enter [1]; rw [l46 sK2 sK0 sK1]
  have l49 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK2) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [← l47 sK2 sK0]
  have l50 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l48 sK2 sK0 sK1]
    conv => enter [1]; rw [← l49 sK1 sK2 sK0]
  have l51 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 1]; rw [l43 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK2]
    conv => enter [1, 2]; rw [← l50 sK2 sK0 sK1]
  have l53 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l8 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l50 sK2 sK0 sK1]
  have l54 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l53 sK2 sK0 sK1]
    conv => enter [1]; rw [l36 sK2 sK0 (sK0 ◇ sK1)]
  have l55 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [← l33 sK2 sK0 (sK0 ◇ sK1)]
  have l56 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l54 sK2 sK0 sK1]
    conv => enter [1]; rw [← l51 sK2 sK0 (sK0 ◇ sK1)]
  have l57 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l55 sK0 sK1 sK2]
  have l58 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [l56 sK2 sK0 sK1]
  have l59 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l58 sK2 sK0 sK1]
  have l60 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l59 sK2 sK0 sK1]
  have l61 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l60 sK2 sK0 sK1]
  have l62 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1 sK2]
    conv => enter [1]; rw [l61 sK2 sK0 sK1]
  have l63 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l62 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l64 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l57 sK1 sK2 sK0]
    conv => enter [1]; rw [l63 sK1 sK0 sK2]
  have l65 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l64 sK1 sK2 sK0]
  have l66 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l65 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (sK0 ◇ sK1) X0]
  have l67 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))]
  have l68 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) ◇ (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))]
  have l69 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l68 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) ◇ (sK0 ◇ sK1))]
  have l70 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l67 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((sK0 ◇ sK1) ◇ (X0 ◇ X1))]
  have l71 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l69 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) ◇ (sK0 ◇ sK1))]
  have l72 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l71 sK1 sK2 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) (sK0 ◇ sK1)]
  have l73 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l72 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [l66 sK1 sK2 sK0 (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) ◇ (sK0 ◇ sK1))]
  have l74 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ sK1))))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l73 sK1 sK2 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (sK0 ◇ sK1)]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l74 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l75 x y z]

theorem Equation4512_41999_implies_Equation42207 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41999 : Equation41999 G) : Equation42207 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41999 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41999 (X1 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h41999 X0 X1 X1]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l0 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l2 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (((X0 ◇ (X0 ◇ X1)) ◇ X0) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41999 X1 X2 X0]
    conv => enter [1]; rw [← l1 (X0 ◇ (X0 ◇ X1)) X0 X2]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X0]
    conv => enter [1]; rw [← h4512 (X0 ◇ (X0 ◇ X1)) X0 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ X2)]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X2)]
  intro x y z
  conv => enter [1]; rw [l3 x y x x]
  conv => enter [1]; rw [l7 y (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ x)))))) z]
  conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 x x x]
  conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 x x ((x ◇ x) ◇ x)]
  conv => enter [1, 2, 2, 2, 2]; rw [h4512 x x ((x ◇ x) ◇ ((x ◇ x) ◇ x))]
  conv => enter [1, 2, 2, 2]; rw [← h41999 x z (x ◇ x)]

theorem Equation4512_42207_implies_Equation41999 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42207 : Equation42207 G) : Equation41999 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [h42207 sK0 X1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h42207 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK2 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h42207 sK1 (sK2 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0 sK1 X0]
  have l4 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h42207 X0 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK0) (X0 ◇ sK2)]
  have l5 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l4 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK0)) (X0 ◇ sK2)]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h42207 (sK0 ◇ sK1) sK2 sK1]
  have l7 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (sK1 ◇ (X0 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l1 sK0 X1 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK1 ◇ X0) ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l8 : ∀ sK0 X1 sK1 X0 : G, (sK0 ◇ X1) = (sK1 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 X1 sK1 X0
    conv => enter [1]; rw [l7 sK0 X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 X0 (X1 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 (sK0 ◇ sK1) sK2 sK0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h42207 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h42207 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0 sK1 sK2]
  have l12 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l11 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK0) ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))))]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0 (sK2 ◇ sK0)]
  have l14 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (sK1 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0))))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l12 sK2 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK2 ◇ sK0) (X0 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)))]
  have l15 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK0 ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l14 sK2 sK0 X0 sK2]
    conv => enter [1]; rw [← l8 sK0 X0 sK2 (sK2 ◇ sK0)]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l17 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l18 : ∀ X0 sK2 sK0 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro X0 sK2 sK0 X1
    conv => enter [1]; rw [h42207 X0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) X1]
    conv => enter [1, 2, 2]; rw [l15 sK2 sK0 (X0 ◇ X1)]
  have l19 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ sK0) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l18 X0 sK2 sK0 X0]
    conv => enter [1]; rw [← h42207 X0 sK0 X0]
  have l20 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h42207 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h42207 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK0 ◇ sK1)]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l19 sK0 sK2 sK0]
    conv => enter [1]; rw [l21 sK0 sK2 sK1]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42207 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l17 sK1 sK2 sK0 sK0]
  have l25 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h42207 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l20 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l25 sK1 sK2 sK0 X0]
  have l27 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h42207 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l17 sK1 sK2 sK0 X0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l26 sK0 sK1 X0 sK0]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1 sK0]
    conv => enter [1]; rw [← h42207 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l13 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l31 x y z]

@[equational_result]
theorem Equation42197_implies_Equation42077 (G : Type*) [Magma G] (h42197 : Equation42197 G) : Equation42077 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42197 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [h42197 sK0 (sK2 ◇ sK1) sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h42197 sK2 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_42077_implies_Equation42197 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h42077 : Equation42077 G) : Equation42197 G := by
  have l0 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [h42077 X1 ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l1 : ∀ X2 X0 X3 X1 : G, (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X1)))) = (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X3 X1
    conv => enter [1]; rw [h42077 X2 (X0 ◇ (X3 ◇ (X3 ◇ X1))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h42077 X0 X1 X3]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h42077 X2 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h42077 X0 X1 X0]
  have l3 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [h42077 sK1 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK2) ((sK0 ◇ sK2) ◇ X0)]
  have l4 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h42077 sK0 X0 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)]
  have l5 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h42077 sK0 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)]
  have l6 : ∀ sK2 X0 sK0 : G, (sK2 ◇ X0) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h42077 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ X0))]
  have l7 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0))) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l0 X1 sK1 sK0 sK2 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l8 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1]; rw [← h42077 sK2 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1]; rw [← h42077 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l10 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h42077 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK0]
    conv => enter [1, 2, 2]; rw [← h42077 sK0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l11 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1, 2]; rw [l8 sK0 sK2 sK1]
  have l12 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l11 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK0 ◇ sK2))]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [l9 sK0 sK1 sK2]
  have l14 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 X0]
  have l15 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [l12 sK1 sK0 sK2]
  have l16 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l17 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l10 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l18 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l10 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l19 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l12 sK1 sK0 sK2]
    conv => enter [1]; rw [l18 sK1 sK0 sK2]
  have l20 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l17 sK2 sK0 sK1]
  have l21 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
  have l22 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [l21 sK1 sK0 sK2]
  have l23 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l22 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
  have l24 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h42077 sK2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ sK2))]
  have l25 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h42077 (sK1 ◇ (sK0 ◇ sK2)) sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK2))]
  have l26 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [h42077 X0 (sK0 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1, 2, 2]; rw [← h42077 sK0 sK2 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l24 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ sK2))]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [l26 (sK1 ◇ (sK0 ◇ sK2)) sK0 sK2]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
  have l30 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l29 sK1 sK2 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l30 sK1 sK2 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h42077 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
  have l34 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) X0]
  have l35 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l34 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
  have l36 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l35 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0]
  have l37 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l36 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l7 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK1 sK0 sK2 X0]
  have l38 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1]; rw [l37 sK1 sK2 sK0 X0]
  have l39 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ X1) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) ◇ X1)) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1, 1]; rw [l4 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) X1]
  have l40 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ X1) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l39 sK0 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) X1]
  have l41 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l40 sK0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [l23 sK1 sK0 sK2 (((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1)]
  have l42 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l41 sK0 X0 X1 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK2)) X0 X1]
  have l43 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ X0) ◇ X1) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [l42 sK0 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l38 sK1 sK2 sK0 (X0 ◇ X1)]
  have l44 : ∀ sK0 X0 X1 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l43 sK0 X0 X1 sK1 sK2]
  have l45 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK2 sK0]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [← l14 sK1 sK0 sK2 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l47 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h42077 X0 ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l46 sK0 sK1 sK2]
  have l48 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) sK0]
    conv => enter [1, 2, 2]; rw [← h42077 sK0 (sK1 ◇ (sK0 ◇ sK2)) sK0]
  have l49 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l6 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK2) (sK0 ◇ (sK0 ◇ X0))]
  have l50 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l49 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK0 ◇ sK2)) sK0 X0]
  have l51 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l50 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ X0)]
  have l52 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
    conv => enter [1]; rw [← l48 sK2 sK0 sK1]
  have l53 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l51 sK1 sK2 X0 sK0]
  have l54 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l52 sK2 sK1 sK0]
    conv => enter [1]; rw [← h42077 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
  have l55 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h42077 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) sK2]
    conv => enter [1, 2, 2, 2]; rw [← l52 sK2 sK1 sK0]
  have l56 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h42077 X0 (sK1 ◇ (sK0 ◇ sK2)) sK2]
    conv => enter [1]; rw [← l55 X0 sK0 sK1 sK2]
  have l57 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l54 sK0 sK2 sK1]
  have l58 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l57 sK0 sK2 sK1]
  have l59 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [← l57 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l60 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1]; rw [l59 sK2 sK0 sK1 X0]
  have l61 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l58 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l62 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l61 sK1 sK0 sK2]
  have l63 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) (sK1 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l61 sK1 sK0 sK2]
  have l64 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l63 sK1 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l62 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 (sK1 ◇ sK2) sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [l65 sK0 sK1 sK2]
  have l67 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h42077 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2)) sK0]
    conv => enter [1]; rw [← l66 sK0 sK1 sK2]
  have l68 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [← l53 sK1 sK2 (sK0 ◇ sK2) sK0]
  have l69 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2 sK1 sK2]
    conv => enter [1, 2, 2]; rw [l68 sK1 sK0 sK2]
  have l70 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l69 sK0 sK2 sK1]
    conv => enter [1]; rw [l23 sK1 sK0 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2))]
  have l71 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h42077 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1, 2]; rw [← l56 X0 sK1 sK0 sK2]
  have l72 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X1)) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1, 1]; rw [l71 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X1]
  have l73 : ∀ X0 sK0 sK1 sK2 X1 : G, ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [l72 X0 sK0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l74 : ∀ X0 sK0 sK1 sK2 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) := by
    intro X0 sK0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X1]
    conv => enter [1]; rw [l73 X0 sK0 sK1 sK2 X1]
  have l75 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l67 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l67 sK1 sK2 sK0]
  have l76 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l3 sK1 ((sK0 ◇ sK2) ◇ X0) sK0 sK2]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) X0]
  have l77 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h42077 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 X1 (X1 ◇ X2)]
  have l78 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) sK1 sK2]
    conv => enter [1, 2]; rw [← l2 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l79 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [l4 sK0 (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l2 X0 (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l80 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X3 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h42077 X3 (X0 ◇ (X1 ◇ X2)) X1]
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1 X2]
  have l81 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X3 ◇ (X0 ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l80 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h42077 X0 X2 X1]
  have l82 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [l79 sK0 X0 sK1 sK2 X1]
    conv => enter [1]; rw [l23 sK1 sK0 sK2 (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)))]
  have l83 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l78 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l64 sK1 sK0 sK2 ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0))]
  have l84 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l76 sK1 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← l3 sK1 X0 sK0 sK2]
  have l85 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l47 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) sK1 sK2 sK0]
    conv => enter [1]; rw [l75 X0 sK0 sK1 sK2]
  have l86 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [l82 sK0 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0 (sK1 ◇ (sK0 ◇ sK2)) X1]
  have l87 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l77 (sK1 ◇ sK2) X0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [← l83 sK0 sK1 sK2 X0]
  have l88 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK2) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l84 sK1 sK0 sK2 X0]
  have l89 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l85 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l81 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) X0 (sK1 ◇ sK2) (sK1 ◇ (sK0 ◇ sK2))]
  have l90 : ∀ sK0 X0 sK1 sK2 X1 : G, (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1))))) := by
    intro sK0 X0 sK1 sK2 X1
    conv => enter [1]; rw [l86 sK0 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [l16 sK1 sK0 sK2 ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1))]
  have l91 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l16 sK1 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1]; rw [l89 X0 sK1 sK0 sK2]
  have l92 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1))) = (sK0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l44 sK0 (sK1 ◇ (sK0 ◇ sK2)) (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← l90 sK0 X0 sK1 sK2 X1]
  have l93 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2, 2]; rw [← l12 sK1 sK0 sK2]
    conv => enter [1]; rw [l91 X0 sK1 sK2 sK0]
  have l94 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l92 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l74 X0 sK0 sK1 sK2 X1]
  have l95 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1]; rw [l94 sK0 sK1 sK2 X0 X1]
  have l96 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l87 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) X0]
  have l97 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ X0) sK0 sK2]
    conv => enter [1, 2, 2]; rw [← l88 sK1 sK0 sK2 X0]
  have l98 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l97 sK1 X0 sK0 sK2]
    conv => enter [1]; rw [← l60 sK2 sK0 sK1 ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)]
  have l99 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l57 sK0 sK2 sK1]
    conv => enter [1]; rw [← l88 sK1 sK0 sK2 (sK0 ◇ sK2)]
  have l100 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l98 sK1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [l95 sK0 sK1 sK2 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l101 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ X0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l100 sK1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [l23 sK1 sK0 sK2 X0]
  have l102 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l101 sK1 X0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← l96 sK1 sK2 X0 sK1]
  have l103 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l99 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2)]
  have l104 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l103 sK0 sK2 sK1]
    conv => enter [1]; rw [← l30 sK1 sK2 sK0]
  have l105 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [l104 sK0 sK2 sK1]
  have l106 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 sK1]
    conv => enter [1]; rw [l105 sK0 sK2 sK1]
  have l107 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l106 sK2 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 sK2]
  have l108 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l107 sK0 sK2 sK1]
    conv => enter [1]; rw [← l96 sK1 sK2 (sK0 ◇ sK2) sK0]
  have l109 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))]
    conv => enter [1]; rw [l108 sK0 sK2 sK1]
  have l110 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l8 sK0 sK2 sK1]
    conv => enter [1]; rw [l109 sK0 sK2 sK1]
  have l111 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l70 sK0 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← l110 sK2 sK1 sK0]
  have l112 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l111 sK0 sK2 sK1]
    conv => enter [1]; rw [← l93 sK2 sK1 sK2 sK0]
  have l113 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l112 sK0 sK2 sK1]
    conv => enter [1]; rw [← l102 sK1 (sK1 ◇ (sK0 ◇ sK2)) sK2]
  have l114 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h42077 X0 (sK1 ◇ (sK0 ◇ sK2)) sK1]
    conv => enter [1, 2, 2]; rw [← l113 sK0 sK2 sK1]
  have l115 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h42077 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l114 sK1 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l115 x y z]

theorem Equation4512_53823_implies_Equation53851 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53823 : Equation53823 G) : Equation53851 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53823 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53823 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h53823 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53823 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53823 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1, 2]; rw [← l24 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l26 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h53823 sK2 sK1]
    conv => enter [1]; rw [h53823 sK2 sK2]
    conv => enter [1, 2]; rw [h53823 sK2 sK1]
  have l31 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
  have l32 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l9 sK2 sK1 ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l20 sK0 (sK2 ◇ (sK2 ◇ sK1))]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l20 sK0 (sK2 ◇ (sK2 ◇ sK1))]
  have l34 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l32 sK2 sK1 sK0]
  have l35 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l34 sK1 sK2 sK0]
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
  have l36 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l35 sK2 sK1 sK0]
  have l37 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l36 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53823 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l28 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l38 sK0 X0]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l39 sK0 X0]
  have l41 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0]
    conv => enter [1]; rw [l40 sK0 X0]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l41 sK0 X0]
  have l43 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l44 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l43 sK2 sK0 sK1]
    conv => enter [1]; rw [l37 sK2 sK1 sK0 sK1]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK0]
    conv => enter [1]; rw [← l44 sK2 sK0 sK0]
  have l46 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h53823 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK2]
  have l47 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [← l46 sK2 sK0]
  have l48 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53823 sK2 sK1]
    conv => enter [1]; rw [← l47 sK0 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l48 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l49 x y z]

theorem Equation4512_53851_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53851 : Equation53851 G) : Equation53823 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53851 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation53824_implies_Equation53853 (G : Type*) [Magma G] (h53824 : Equation53824 G) : Equation53853 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h53824 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h53824 sK1 X0 sK1]
  have l1 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h53824 sK1 X0 sK1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l1 X0 X0 sK1]
    conv => enter [1]; rw [← h53824 sK1 X0 sK1]
  have l3 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l2 sK1 sK3]
    conv => enter [1]; rw [h53824 sK3 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_53853_implies_Equation53824 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53853 : Equation53853 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53853 sK0 X0 sK0 sK2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53826_implies_Equation53847 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53826 : Equation53826 G) : Equation53847 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) X0]
  have l14 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l15 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53826 X1 X0]
    conv => enter [1]; rw [h53826 X1 X2]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53826 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53826 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l19 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53826 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53826 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) (sK2 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h53826 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h53826 (sK0 ◇ sK0) sK0]
  have l23 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h53826 X0 X1]
  have l24 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l23 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l25 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK2 (sK1 ◇ sK1)]
  have l27 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l20 sK1 sK2]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l30 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l31 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l24 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l32 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l33 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l26 sK2 sK1]
    conv => enter [1]; rw [h53826 sK2 sK1]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l27 sK1 sK2]
  have l35 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l38 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l31 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l39 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l40 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l37 sK0]
  have l42 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l38 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l39 sK0]
  have l44 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l40 sK0]
  have l45 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l43 sK0]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l41 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l41 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l48 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [l46 sK0]
  have l49 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l48 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l48 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l51 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [l49 sK0]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l51 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l53 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l35 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l54 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l14 sK2 sK1]
    conv => enter [1]; rw [l53 sK2 sK1]
  have l55 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l33 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK1]
    conv => enter [1]; rw [h53826 (sK1 ◇ sK1) sK0]
  have l57 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h53826 X0 X1]
    conv => enter [1]; rw [h53826 X0 sK0]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l56 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK1]
    conv => enter [1]; rw [l58 sK1 sK0]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l61 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1]; rw [l60 sK1 sK0]
  have l62 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l13 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l54 sK2 sK1]
  have l63 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l54 sK2 sK1]
  have l64 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l63 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) sK1]
  have l65 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l62 sK1 sK2]
    conv => enter [1]; rw [l13 sK1 sK2 sK1]
  have l66 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l33 sK1 sK2]
    conv => enter [1]; rw [l65 sK1 sK2]
  have l67 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))]
  have l68 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l67 sK1 sK2]
  have l69 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1]; rw [l68 sK1 sK2]
  have l70 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [h53826 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l71 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l70 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l72 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l71 sK1 X0 sK0]
  have l73 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l45 sK0]
    conv => enter [1]; rw [← l39 sK0]
  have l74 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0 sK0]
    conv => enter [1]; rw [← l73 sK0]
  have l75 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l48 sK0]
    conv => enter [1]; rw [← l74 sK0]
  have l76 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l75 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l77 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l55 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))]
  have l78 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l77 sK2 sK1]
    conv => enter [1, 2]; rw [l64 sK1 sK2]
  have l79 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l15 sK2 sK1]
    conv => enter [1]; rw [l78 sK2 sK1]
  have l80 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l79 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l81 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l80 sK1 sK2]
  have l82 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l76 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l83 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l52 sK0 X0]
    conv => enter [1]; rw [← l82 sK0 X0]
  have l84 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l83 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l85 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l84 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l86 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0]
    conv => enter [1]; rw [← l85 sK0]
  have l87 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h53826 X0 sK0]
    conv => enter [1]; rw [h53826 X0 sK1]
  have l88 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [h53826 (sK0 ◇ sK0) sK1]
  have l89 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l88 sK0 sK1]
    conv => enter [1]; rw [← l72 sK1 (sK1 ◇ sK1) sK0]
  have l90 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l89 sK0 sK1]
    conv => enter [1]; rw [l87 sK1 (sK1 ◇ sK1) sK0]
  have l91 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← l90 sK0 sK1]
  have l92 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l91 sK1 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0)]
  have l93 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l92 sK1 sK0]
  have l94 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0]
    conv => enter [1]; rw [l93 sK0 sK1]
  have l95 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l14 sK2 sK1]
    conv => enter [1, 2]; rw [l94 sK1 sK0]
  have l96 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l94 sK1 sK0]
  have l97 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l96 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [l97 sK0 sK1]
  have l99 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [l98 sK1 sK0]
  have l100 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l99 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l101 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l95 sK2 sK1 sK0]
    conv => enter [1]; rw [l100 sK2 sK0 sK1]
  have l102 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l101 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l103 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l102 sK1 sK2 sK0]
  have l104 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53826 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l16 X1 (X1 ◇ X1) X0]
  have l105 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l104 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X1 (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0)))]
  have l106 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (sK0 ◇ ((X1 ◇ X1) ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0
    conv => enter [1]; rw [l105 X1 X1]
    conv => enter [1, 2, 2]; rw [l57 X1 (X1 ◇ X1) sK0]
  have l107 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (sK0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))))) := by
    intro X1 sK0
    conv => enter [1]; rw [l106 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 (sK0 ◇ sK0)]
  have l108 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0
    conv => enter [1]; rw [l107 X1 sK0]
    conv => enter [1, 2]; rw [← l42 sK0 (sK0 ◇ sK0) X1]
  have l109 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0
    conv => enter [1]; rw [l108 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l110 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l109 X1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0)]
  have l111 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0
    conv => enter [1]; rw [l110 X1 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l112 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [l111 X1 sK0]
    conv => enter [1, 2]; rw [← l48 sK0]
  have l113 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h53826 X0 sK1]
    conv => enter [1]; rw [l112 X0 sK0]
  have l114 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l64 sK1 sK2]
    conv => enter [1]; rw [l113 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) sK0]
  have l115 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l103 sK1 sK2 sK1]
    conv => enter [1]; rw [← l114 sK1 sK2 sK1]
  have l116 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l66 sK1 sK2]
    conv => enter [1]; rw [← l115 sK1 sK2]
  have l117 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l81 sK1 sK2]
    conv => enter [1, 2]; rw [← l116 sK1 sK2]
  have l118 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l117 sK1 sK2]
    conv => enter [1]; rw [l112 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) sK0]
  have l119 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l103 sK1 sK2 sK1]
    conv => enter [1]; rw [← l118 sK1 sK2 sK1]
  have l120 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l69 sK1 sK2]
    conv => enter [1]; rw [← l119 sK1 sK2]
  have l121 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l116 sK1 sK2]
    conv => enter [1]; rw [← l120 sK1 sK2]
  have l122 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l94 sK0 sK1]
    conv => enter [1]; rw [← l121 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l122 x y z]

theorem Equation4512_53847_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53847 : Equation53847 G) : Equation53826 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53847 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53847 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l8 sK0 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53847 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53847 X0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l16 X0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l17 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l19 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h53847 X0 X1 X1]
    conv => enter [1, 2]; rw [l15 X1 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l15 sK1 sK1 sK0]
  have l32 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 sK1]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 sK0]
    conv => enter [1]; rw [← l28 sK0 sK0]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 X0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 sK1]
    conv => enter [1]; rw [l32 sK1 sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l37 : ∀ X1 sK0 sK1 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X1 sK0 sK1
    conv => enter [1]; rw [← l34 X1 X1 sK0]
    conv => enter [1]; rw [l15 X1 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l35 sK1 sK0]
  have l39 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l37 X1 sK0 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1, 2]; rw [← l36 sK0]
  have l41 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [l39 sK0 X1]
    conv => enter [1, 2]; rw [← l36 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l40 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l44 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h53847 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 2, 2]; rw [← l43 sK0 sK1]
  have l45 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l44 X0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l41 sK0 X0]
  have l46 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l45 X0 X0 sK0]
    conv => enter [1]; rw [← l41 sK0 (X0 ◇ X0)]
  have l47 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X1))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h53847 X1 X1 X2]
    conv => enter [1]; rw [l46 X1 sK0]
  intro x y
  conv => enter [1]; rw [← l47 y x x]

theorem Equation4512_53827_implies_Equation53849 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53827 : Equation53827 G) : Equation53849 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l3 sK1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l5 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK1 X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53827 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l6 sK1 X0]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1]
    conv => enter [1]; rw [← h53827 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) sK1]
  have l9 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1]
  have l10 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l10 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [← h53827 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [← l13 sK1 X0]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53827 X0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l14 sK1 (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))]
  have l16 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1]; rw [h53827 X0 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l16 x y z w]

theorem Equation4512_53849_implies_Equation53827 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53849 : Equation53849 G) : Equation53827 G := by
  have l0 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [h53849 X1 X2 X3 (X2 ◇ X2)]
    conv => enter [1, 2, 2]; rw [h53849 X2 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53849 sK0 sK0 X0 sK0]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53849 X0 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l4 : ∀ sK0 sK1 sK2 X2 X3 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2 X2 X3 X0
    conv => enter [1]; rw [← l2 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 X2 X3 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 X2 X3 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X2 X3
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X2 X3 sK0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK0]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l7 : ∀ X2 X3 X4 sK0 X0 : G, (X2 ◇ (X3 ◇ (X2 ◇ X4))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 X4 sK0 X0
    conv => enter [1]; rw [← h53849 X2 X2 X3 X4]
    conv => enter [1]; rw [h53849 X2 sK0 X0 (sK0 ◇ sK0)]
  have l8 : ∀ X2 X3 X4 sK0 sK1 sK2 : G, (X2 ◇ (X3 ◇ (X2 ◇ X4))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro X2 X3 X4 sK0 sK1 sK2
    conv => enter [1]; rw [l7 X2 X3 X4 sK0 X2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 sK0 X2]
  have l9 : ∀ sK0 X2 X3 X4 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro sK0 X2 X3 X4
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 X2 X3 X4 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y x z]

theorem Equation4512_53855_implies_Equation53829 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53855 : Equation53855 G) : Equation53829 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53855 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53855 X0 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X3 ◇ X1))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [h53855 sK0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l3 x y x z]

theorem Equation4512_53829_implies_Equation53855 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53829 : Equation53829 G) : Equation53855 G := by
  have l0 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK2 (sK3 ◇ (sK0 ◇ sK2))]
  have l1 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK3 ◇ (sK0 ◇ sK2)) X0]
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
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53829 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53829 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53829 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 sK1 X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53829 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l3 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53829 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l5 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l12 sK1 X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 X0]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h53829 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l10 sK1 sK1]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l5 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 sK1 X0]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l7 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 X0]
  have l20 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l7 sK1]
    conv => enter [1]; rw [l16 sK1 X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l17 sK1 X0]
  have l23 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l18 sK1 X0]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1, 2]; rw [l7 sK1]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l21 sK1 X0]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l19 sK1 sK1]
    conv => enter [1]; rw [← l23 sK1 sK1]
  have l27 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1 sK1]
    conv => enter [1]; rw [← l25 sK1 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [← l26 sK1]
  have l30 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l29 sK1]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l30 sK1]
  have l32 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l28 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l33 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53829 X0 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l22 sK1 X0]
  have l34 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l22 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))]
  have l35 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1, 2]; rw [l22 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))]
    conv => enter [1]; rw [l1 sK0 sK2 sK3 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2))))]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h53829 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK2)) sK2]
  have l37 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l34 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← h53829 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l32 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l39 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l37 sK1 X0]
    conv => enter [1, 2]; rw [← l32 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l26 sK1]
  have l41 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l39 sK1 X0]
    conv => enter [1, 2]; rw [← l26 sK1]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l31 sK1]
  have l43 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l41 sK1 X0]
    conv => enter [1, 2]; rw [← l31 sK1]
  have l44 : ∀ X1 X0 X2 sK2 sK0 : G, (X1 ◇ (X0 ◇ (X2 ◇ X1))) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 X0 X2 sK2 sK0
    conv => enter [1]; rw [← h53829 X0 X1 X2]
    conv => enter [1]; rw [h53829 X0 sK2 sK0]
  have l45 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [h53829 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK2 (X0 ◇ (sK0 ◇ sK2))]
  have l46 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l45 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l33 X0 sK1]
  have l47 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l43 sK1 X0]
    conv => enter [1]; rw [← l46 sK0 sK2 X0 sK1]
  have l48 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l42 sK0 sK1 sK2]
    conv => enter [1]; rw [l47 sK0 sK1 sK2 X0]
  have l49 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l43 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l48 sK0 sK2 sK1 X0]
  have l50 : ∀ sK1 sK0 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l49 sK1 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l51 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l50 sK1 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [l44 (sK0 ◇ sK2) X0 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l51 x y z w]

theorem Equation4512_53855_implies_Equation53843 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53855 : Equation53855 G) : Equation53843 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53855 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53855 X0 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53855 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53843_implies_Equation53855 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53843 : Equation53843 G) : Equation53855 G := by
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
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53843 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53843 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l6 sK1 X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53843 sK1 (sK1 ◇ sK1) X0]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l5 sK1]
    conv => enter [1]; rw [l9 sK1 X0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 X0]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← l12 sK1 sK1]
  have l15 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l15 sK1]
    conv => enter [1]; rw [h53843 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l15 sK1]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [l16 sK1 X0]
  have l18 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53843 sK1 (X0 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 2, 2]; rw [← h53843 sK1 sK1 X0]
  have l19 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l18 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 sK1]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l20 sK1 X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1 X0]
  have l23 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h53843 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 2, 2]; rw [← l22 sK1 X0]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l23 X0 sK1 X0]
    conv => enter [1]; rw [← l17 sK1 X0]
  have l25 : ∀ X1 X2 X0 sK1 : G, (X1 ◇ (X2 ◇ (X0 ◇ X1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 X0 sK1
    conv => enter [1]; rw [← h53843 X0 X1 X2]
    conv => enter [1]; rw [l24 X0 sK1]
  intro x y z w
  conv => enter [1]; rw [← l25 y z w x]

theorem Equation4512_53830_implies_Equation53857 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53830 : Equation53830 G) : Equation53857 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53830 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h53830 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 X0]
  have l5 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1]; rw [h53830 sK3 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_53857_implies_Equation53830 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53857 : Equation53857 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h53857 X0 X1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [h53857 sK0 X1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53858_implies_Equation53831 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53831 G := by
  have l0 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK3 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK3 ◇ sK0)]
  have l1 : ∀ sK1 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK3 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK3 ◇ sK0)) X0]
  have l2 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53858 sK1 X0 X1 sK1 sK1]
  have l3 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [h53858 X0 sK1 (sK3 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h53858 X0 sK2 (sK1 ◇ (sK3 ◇ sK0)) sK1 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK1)]
  have l5 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [h53858 X0 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK3 sK0 (sK1 ◇ sK1)]
  have l6 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK3 sK3 sK0 sK1]
    conv => enter [1]; rw [l4 sK3 sK2 sK1 sK3 sK0]
  have l7 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [← l3 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [l5 sK1 sK3 sK0 sK1]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 X0 X1]
  have l9 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK1 sK3 sK0]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK2 sK1 sK3 sK0]
  have l11 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [← l6 sK3 sK0 sK1 sK1]
  have l12 : ∀ sK1 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK3 sK0]
    conv => enter [1]; rw [l1 sK1 sK3 sK0 (sK1 ◇ sK1)]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l12 sK1 sK1 sK1]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK1 sK1 sK1]
  have l15 : ∀ X1 X2 X3 X4 X0 sK1 : G, (X1 ◇ (X2 ◇ (X3 ◇ X4))) = ((X0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X1 X2 X3 X4 X0 sK1
    conv => enter [1]; rw [← h53858 (X0 ◇ (sK1 ◇ sK1)) X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← l8 sK1 (X0 ◇ (sK1 ◇ sK1)) X0]
  have l16 : ∀ X1 X2 X3 X4 X0 sK1 : G, (X1 ◇ (X2 ◇ (X3 ◇ X4))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 X3 X4 X0 sK1
    conv => enter [1]; rw [l15 X1 X2 X3 X4 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ X1 X2 X3 X4 X0 sK1 : G, (X1 ◇ (X2 ◇ (X3 ◇ X4))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X1 X2 X3 X4 X0 sK1
    conv => enter [1]; rw [l16 X1 X2 X3 X4 X0 sK1]
    conv => enter [1, 2]; rw [← l13 sK1]
  have l18 : ∀ sK1 X1 X2 X3 X4 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 X1 X2 X3 X4
    conv => enter [1]; rw [l14 sK1 sK1]
    conv => enter [1]; rw [← l17 X1 X2 X3 X4 sK1 sK1]
  intro x y z w
  conv => enter [1]; rw [l18 x y x z w]

theorem Equation4512_53831_implies_Equation53858 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53831 : Equation53831 G) : Equation53858 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ sK2 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l5 : ∀ sK2 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l6 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53831 (sK2 ◇ sK2) sK2 X0 X1]
  have l7 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h53831 sK2 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [← l1 sK2 (X0 ◇ X1)]
  have l8 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l7 sK2 X0 X1]
  have l9 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l6 sK2 X0 X1]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2)]
  have l10 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l8 sK2 X0 X1]
  have l11 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l9 sK2 X0 X1]
    conv => enter [1, 2]; rw [l5 sK2]
  have l12 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l11 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ (sK2 ◇ sK2))]
  have l13 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l10 sK2 sK2 sK2]
    conv => enter [1]; rw [l12 sK2 sK2 sK2]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l13 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l15 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [← l14 sK2 X0]
  have l16 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l15 sK2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← h53831 X0 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l17 : ∀ sK2 X1 X0 X2 X3 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l16 sK2 X0]
    conv => enter [1]; rw [h53831 X0 X1 X2 X3]
  intro x y z w u
  conv => enter [1]; rw [l17 x y z w u]

theorem Equation4512_53858_implies_Equation53845 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53858 : Equation53858 G) : Equation53845 G := by
  have l0 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53858 sK1 X0 X1 sK1 sK0]
  have l1 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 X0 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_53845_implies_Equation53858 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53845 : Equation53845 G) : Equation53858 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [l1 sK2 X0]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ X0)]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h53845 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [← l4 sK2 X0]
  have l6 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ sK2) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l5 sK2 X0]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l6 sK2 X0]
  have l8 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l7 sK2 X0]
  have l9 : ∀ sK2 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [← l8 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 X1]
  have l10 : ∀ sK2 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X1
    conv => enter [1]; rw [l7 sK2 (sK2 ◇ X1)]
    conv => enter [1]; rw [← l9 sK2 X1 sK2]
  have l11 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2 (sK2 ◇ (X0 ◇ sK2))]
    conv => enter [1]; rw [← h53845 X0 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK2]
  have l12 : ∀ sK2 X0 X1 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK1]
    conv => enter [1]; rw [h53845 sK1 X0 X1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l12 x y z w u]

theorem Equation4512_53833_implies_Equation53839 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53833 : Equation53833 G) : Equation53839 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53833 (sK0 ◇ sK0) sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53833 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h53833 X0 X1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53833 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l14 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l12 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53833 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53833 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l14 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53833 sK2 sK1]
    conv => enter [1]; rw [l13 sK2 sK0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0]
  have l24 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l19 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l28 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l24 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l29 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l26 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l18 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l18 sK0]
    conv => enter [1]; rw [h53833 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l18 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l30 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l32 sK0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l36 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2, 2]; rw [l33 sK0]
    conv => enter [1]; rw [← h53833 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l37 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l13 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l36 sK0]
  have l38 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l38 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l39 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l34 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l41 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l44 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l8 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 sK0]
  have l45 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK1 sK2 sK0]
  have l46 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l42 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l44 sK0 sK2 sK1]
  have l47 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l46 sK0 sK2 sK1]
    conv => enter [1]; rw [l45 sK0 sK2 sK1]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l13 X0 sK0]
    conv => enter [1]; rw [h53833 X0 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [l13 X0 sK0]
  have l49 : ∀ X0 X1 sK0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X1]
  have l50 : ∀ X0 X1 sK0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l49 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l51 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))]
  have l52 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l50 X0 X1 sK0]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l51 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))]
  have l54 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l52 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1]; rw [← l28 X0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) X0]
  have l56 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l55 sK0 X0]
    conv => enter [1, 2]; rw [← l28 (sK0 ◇ sK0) sK0 X0]
  have l57 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l56 sK0 X0]
    conv => enter [1, 2]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l58 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l57 sK0 X0]
    conv => enter [1, 2]; rw [← l35 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l59 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l58 sK0 X0]
    conv => enter [1, 2]; rw [l8 sK0 sK0]
  have l60 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l59 sK0 X0]
    conv => enter [1, 2]; rw [← l42 sK0 sK0]
  have l61 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l60 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l62 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l61 sK0 X0]
    conv => enter [1, 2]; rw [← l25 sK0]
  have l63 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK0]
    conv => enter [1]; rw [l62 sK0 sK2]
  have l64 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [l62 sK0 X0]
  have l65 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1)) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l62 sK0 X0]
  have l66 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l65 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l67 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 sK0 X1]
    conv => enter [1]; rw [l66 sK0 X0 X1]
  have l68 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53833 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l63 sK1 sK2 sK0]
  have l69 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l68 sK2 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l70 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l69 sK2 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l13 sK2 sK0]
    conv => enter [1]; rw [l70 sK2 sK0 sK1]
  have l72 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l71 sK0 sK2 sK1]
    conv => enter [1]; rw [l62 sK0 sK2]
  have l73 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK0]
    conv => enter [1]; rw [← l72 sK0 sK1 sK2]
  have l74 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53833 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l73 sK1 sK2 sK0]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [l62 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l77 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
  have l79 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK2 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l80 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK0]
    conv => enter [1]; rw [l79 sK2 sK0 sK1]
  have l81 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l64 (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l82 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l81 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l83 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← l82 sK1 sK2 sK0]
  have l84 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53833 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l83 sK0 sK1 sK2]
  have l85 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l84 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l86 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l85 sK1 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l87 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l86 sK1 sK2 sK0]
    conv => enter [1]; rw [← l28 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK1))]
  have l88 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l87 sK1 sK2 sK0]
    conv => enter [1]; rw [← l54 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l89 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l88 sK1 sK2 sK0]
    conv => enter [1]; rw [l67 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l90 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l89 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l29 sK0]
  have l91 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l90 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l34 sK0]
  have l92 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l13 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1]; rw [l91 sK1 sK2 sK0]
  have l93 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l62 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l92 sK0 sK1 sK2]
  have l94 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [l93 sK1 sK2 sK0]
  have l95 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l80 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l94 sK0 sK1 sK2]
  have l96 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l95 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l97 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l94 sK0 sK1 sK2]
    conv => enter [1]; rw [← l96 sK1 sK2 sK0]
  have l98 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l97 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l99 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l63 sK1 sK2 sK1]
    conv => enter [1]; rw [l98 sK2 sK1 sK1]
  have l100 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h53833 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l99 sK1 sK2]
  have l101 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l100 sK2 sK1]
    conv => enter [1]; rw [l13 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
  have l102 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l101 sK2 sK1 sK0]
    conv => enter [1]; rw [l62 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l103 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← l102 sK2 sK1 sK0]
  have l104 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l103 sK0 sK2 sK1]
    conv => enter [1]; rw [l13 (sK2 ◇ sK1) sK0]
  have l105 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l104 sK0 sK2 sK1]
    conv => enter [1]; rw [l62 sK0 (sK2 ◇ sK1)]
  have l106 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l105 sK0 sK2 sK1]
    conv => enter [1]; rw [← l95 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l106 x y z]

theorem Equation4512_53839_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53839 : Equation53839 G) : Equation53833 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53839 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53834_implies_Equation53841 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53834 : Equation53834 G) : Equation53841 G := by
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
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK1 X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [← h53834 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [← l7 sK1 X1]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53834 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53834 X0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l10 sK1 (X0 ◇ X0)]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l11 sK1 X0]
  have l14 : ∀ sK1 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [← l12 sK3 sK1]
    conv => enter [1]; rw [h53834 sK3 X0 sK0]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53834 sK1 X0 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← l5 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l15 sK1 X0]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l16 sK1 X0]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1 sK1]
    conv => enter [1]; rw [← l18 sK1 sK1]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l20 x y z w]

theorem Equation4512_53841_implies_Equation53834 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53841 : Equation53841 G) : Equation53834 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53841 sK0 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53841 X0 X0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53841 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53836_implies_Equation53837 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53836 : Equation53836 G) : Equation53837 G := by
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
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53836 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l6 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0
    conv => enter [1]; rw [← h53836 X1 X1]
    conv => enter [1]; rw [l5 X1 sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 X1]
    conv => enter [1, 2]; rw [l5 X1 sK0]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0]
    conv => enter [1, 2]; rw [← l11 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0 X0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53836 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l17 X0 sK0]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X1]
    conv => enter [1]; rw [← l18 X0 X1 sK0]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation4512_53837_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53837 : Equation53837 G) : Equation53836 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53837 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53836_implies_Equation53852 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53836 : Equation53836 G) : Equation53852 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53836 X0 X0]
    conv => enter [1]; rw [← h53836 X1 X0]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [l0 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l2 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [l1 X0 sK2]
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
  have l3 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h53836 X0 X1]
    conv => enter [1, 2]; rw [l2 X1 sK2]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK2 sK0]
  have l6 : ∀ sK2 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X1
    conv => enter [1]; rw [l3 sK2 X1 sK2]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 X1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_53852_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53852 : Equation53852 G) : Equation53836 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53852 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l2 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_53844_implies_Equation53856 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53844 : Equation53844 G) : Equation53856 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53844 sK1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53844 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l5 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [← h53844 sK0 X0 sK3]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l6 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h53844 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l4 sK1 X0]
  have l7 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1, 1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
  have l8 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l6 X0 X0 sK1]
    conv => enter [1]; rw [← l7 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [l8 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ X0 sK3 sK0 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK3 sK0 X1
    conv => enter [1]; rw [l5 X0 sK3 sK0 X0]
    conv => enter [1]; rw [← l5 X1 sK3 sK0 X0]
  have l11 : ∀ X0 sK3 sK0 X1 X2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X1 ◇ (X2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK0 X1 X2
    conv => enter [1]; rw [l10 X0 sK3 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK3 ◇ (sK0 ◇ sK3))]
  have l12 : ∀ X0 sK3 sK0 X1 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK3 sK0 X1 sK2
    conv => enter [1]; rw [l11 X0 sK3 sK0 X1 X0]
    conv => enter [1, 2]; rw [l10 X0 sK3 sK0 sK2]
  have l13 : ∀ sK2 sK3 sK0 X1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK2 sK3 sK0 X1
    conv => enter [1]; rw [l12 sK2 sK3 sK0 X1 sK2]
  have l14 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK3)) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l9 sK1 (sK3 ◇ (sK0 ◇ sK3))]
    conv => enter [1, 2]; rw [l10 (sK3 ◇ (sK0 ◇ sK3)) sK3 sK0 sK2]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [← l13 sK2 sK3 sK0 (sK3 ◇ (sK0 ◇ sK3))]
  intro x y z w
  conv => enter [1]; rw [l15 x y z w]

theorem Equation4512_53856_implies_Equation53844 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53856 : Equation53856 G) : Equation53844 G := by
  have l0 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53856 sK0 X0 sK2 sK0]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

end Semigroup5
