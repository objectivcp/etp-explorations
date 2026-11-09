import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4276_4512_41538_41557_41592_41621_implies_Equation41585 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h41538 : Equation41538 G) (h41557 : Equation41557 G) (h41592 : Equation41592 G) (h41621 : Equation41621 G) : Equation41585 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h4276 sK1 sK0]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4276 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [← l12 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41538 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41538 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41538 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4276 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [l15 sK0 sK1 (sK1 ◇ sK1)]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l27 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l28 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l30 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l30 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1 X0]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l42 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l30 sK0 sK1 sK1]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l30 sK0 sK1 sK1]
  have l45 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l36 sK0 sK1 X0]
    conv => enter [1]; rw [← l28 sK0 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)]
  have l46 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l42 sK1 X0 sK0]
    conv => enter [1]; rw [← l45 sK0 sK1 X0]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41557 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l29 sK0 sK1]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l47 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1 sK1]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l46 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) sK0]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 (sK0 ◇ sK0)]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) X0]
  have l55 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l54 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ sK0) X0]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l55 sK0 sK1 X0]
  have l57 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
  have l58 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0]
  have l60 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1]; rw [l58 sK1 sK0 X0]
  have l61 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l62 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
    conv => enter [1, 2]; rw [← l59 sK1 sK0]
  have l66 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0]
    conv => enter [1, 1]; rw [l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l66 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l68 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l67 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l69 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  have l70 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l69 sK1 sK0]
    conv => enter [1]; rw [l10 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l70 sK1 sK0]
    conv => enter [1]; rw [← l56 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l72 sK1 sK0]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l65 sK0 sK1]
    conv => enter [1]; rw [l73 sK0 sK1]
  have l75 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41592 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l77 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l63 sK0 sK1]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l77 sK1 sK0]
    conv => enter [1]; rw [← l27 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) sK0]
  have l79 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l77 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) X0]
  have l80 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l79 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 X0]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 sK0]
  have l82 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l80 sK1 sK0 X0]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l81 sK0 sK1]
  have l84 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) sK1]
  have l85 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) X0]
  have l86 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l85 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0 X0]
  have l87 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l84 sK1 sK0]
    conv => enter [1]; rw [← l60 sK1 sK0 sK0]
  have l88 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l86 sK0 sK1 X0]
  have l89 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l10 sK1 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l87 sK1 sK0]
  have l90 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [l89 sK1 sK0]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l90 sK0 sK1]
  have l92 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l91 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l93 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l92 sK1 sK0]
    conv => enter [1]; rw [← l88 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l94 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← l93 sK1 sK0]
  have l95 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1 sK1]
    conv => enter [1]; rw [l94 sK0 sK1]
  have l96 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l95 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) sK0]
  have l97 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l96 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK0]
  have l98 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l97 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0)]
  have l99 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l98 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1 sK0]
  have l100 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [l99 sK1 sK0]
  have l101 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41621 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l44 sK1 sK0]
  have l102 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l101 sK1 sK0]
    conv => enter [1]; rw [← l68 sK0 sK1 (sK1 ◇ sK1)]
  have l103 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l102 sK1 sK0]
    conv => enter [1, 2]; rw [l100 sK1 sK0]
  have l104 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l103 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l105 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41621 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l104 sK1 sK0]
  have l106 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l105 sK0 sK1]
    conv => enter [1]; rw [← l82 sK1 sK0 (sK1 ◇ sK1)]
  have l107 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l106 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l107 x y]

theorem Equation4276_4512_41538_41548_41557_implies_Equation41585 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h41538 : Equation41538 G) (h41548 : Equation41548 G) (h41557 : Equation41557 G) : Equation41585 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h4276 sK1 sK0]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4276 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4276 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41538 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41538 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ sK1) sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l25 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41538 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l25 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK1 X0]
    conv => enter [1]; rw [l31 sK0 sK1 X0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 sK1]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41548 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l28 sK0 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l38 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41548 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l33 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l39 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1, 2]; rw [← l30 sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1, 2]; rw [← l26 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l35 sK1 sK0]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1 sK1]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l33 sK0 sK1 (sK0 ◇ sK0)]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l47 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l51 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0) X0]
  have l52 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1, 2]; rw [← l46 sK1 sK0]
  have l53 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l52 sK1 sK0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l53 sK1 sK0]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l51 sK1 sK0 sK0]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l60 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41557 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2, 2]; rw [← l60 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) sK0]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l10 sK1 sK0 (sK1 ◇ sK1)]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1, 2]; rw [← l54 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l64 x y]

theorem Equation4276_4512_4695_implies_Equation2 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← h4695 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [h4276 (X1 ◇ (X1 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 : G, (X1 ◇ (X1 ◇ X1)) = X1 := by
    intro X1
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4276 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l9 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4276_4512_4695_implies_Equation4949 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation4949 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4276 X0 sK1]
  have l1 : ∀ sK1 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l2 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2, 2]; rw [h4276 sK1 X0]
    conv => enter [1]; rw [← h4695 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = X0 := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l2 X0 sK1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x (y ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

theorem Equation4276_4512_4695_implies_Equation41999 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation41999 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← h4695 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [h4276 (X1 ◇ (X1 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 : G, (X1 ◇ (X1 ◇ X1)) = X1 := by
    intro X1
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4276 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l9 X1 (X1 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l10 (x ◇ y) (y ◇ (z ◇ (z ◇ (z ◇ x))))]

theorem Equation4276_4512_4695_implies_Equation41790 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation41790 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4276 sK1 X0]
  have l1 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h4276 X0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l2 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1 sK2]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK0 ◇ sK1)) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [h4276 (sK2 ◇ (sK0 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l7 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4695 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4695 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))))))]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK1 ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))))) sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK2 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← l3 sK1 sK2 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4276_4512_4695_implies_Equation41671 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation41671 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4276 X0 sK2]
  have l1 : ∀ X0 X1 sK2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X1]
  have l2 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) = X0 := by
    intro X0 sK2
    conv => enter [1, 2, 2, 2]; rw [h4276 sK2 X0]
    conv => enter [1]; rw [← h4695 X0]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = X0 := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l4 X0 sK2]
  have l6 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = X0 := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← l3 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK2 X0]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = X0 := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l6 sK2 X0]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = X0 := by
    intro sK2 X0
    conv => enter [1]; rw [h4276 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l7 sK2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l9 (x ◇ x) (y ◇ (z ◇ (x ◇ (w ◇ u))))]

theorem Equation4276_4512_4695_implies_Equation54160 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation54160 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← h4695 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [h4276 (X1 ◇ (X1 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 : G, (X1 ◇ (X1 ◇ X1)) = X1 := by
    intro X1
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4276 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l9 X1 (X1 ◇ X1)]
  intro x y z w u v
  conv => enter [1]; rw [l10 (x ◇ (y ◇ x)) (z ◇ (w ◇ (u ◇ v)))]

theorem Equation4276_4512_4695_implies_Equation53905 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation53905 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← h4695 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [h4276 (X1 ◇ (X1 ◇ X1)) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X1 : G, (X1 ◇ (X1 ◇ X1)) = X1 := by
    intro X1
    conv => enter [1]; rw [l3 X1 X1]
    conv => enter [1]; rw [l0 X1 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h4695 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4276 X1 X0]
    conv => enter [1]; rw [l4 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l5 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l9 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l8 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l12 X1 (X1 ◇ X1)]
  intro x y z w
  conv => enter [1]; rw [l13 (x ◇ (x ◇ y)) (y ◇ (x ◇ (z ◇ w)))]

theorem Equation4276_4512_4695_implies_Equation54291 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4512 : Equation4512 G) (h4695 : Equation4695 G) : Equation54291 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4276 X0 sK2]
  have l1 : ∀ X0 X1 sK2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X1]
  have l2 : ∀ sK2 X1 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ X0 sK2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))))) = X0 := by
    intro X0 sK2
    conv => enter [1, 2, 2, 2]; rw [h4276 sK2 X0]
    conv => enter [1]; rw [← h4695 X0]
  have l5 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) = X0 := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l4 X0 sK2]
  have l6 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) = X0 := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← l3 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK2 X0]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = X0 := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [l6 sK2 X0]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = X0 := by
    intro sK2 X0
    conv => enter [1]; rw [h4276 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l7 sK2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l9 (x ◇ (y ◇ y)) (z ◇ (w ◇ (y ◇ x)))]

theorem Equation4276_4343_4512_implies_Equation53826 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) : Equation53826 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4343 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4276 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4343 X1 (X0 ◇ X1)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X1 ◇ X1)]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l3 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4276 sK0 sK1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [h4343 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4276 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4343 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [h4343 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4276 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4343 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l19 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [h4343 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l5 X0 sK0 X0]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4343 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l20 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4343 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4276 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1, 2]; rw [← l27 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4343 sK0 (sK1 ◇ sK1)]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l39 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l40 x y]

theorem Equation4276_4293_4512_implies_Equation53833 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) : Equation53833 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [h4293 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4293 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [h4276 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4276 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X1 ◇ X2))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l9 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l10 X0 X2 X1]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X2) ◇ ((X0 ◇ X2) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [h4293 X1 (X0 ◇ X2)]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X2 ((X0 ◇ X2) ◇ X1)]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X1 X0]
    conv => enter [1, 2]; rw [h4293 X1 X0]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [l15 X2 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1 X1]
    conv => enter [1]; rw [← l2 X1 X1 X1]
  have l18 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ (X2 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l11 X1 X1 X2]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X2 (X2 ◇ X1)]
    conv => enter [1]; rw [← l2 X1 X2 X2]
  intro x y
  conv => enter [1]; rw [l19 x x y]
  conv => enter [1]; rw [l14 x y y]
  conv => enter [1]; rw [← l2 y x y]

theorem Equation4343_4512_53848_implies_Equation53830 (G : Type*) [Magma G] (h4343 : Equation4343 G) (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4343 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53848 X2 X3 X3]
    conv => enter [1, 2]; rw [h53848 X3 X0 X1]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← l2 X3 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l3 y x z x]

theorem Equation4276_4293_4512_53808_53848_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53848 : Equation53848 G) : Equation53834 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4276 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4293 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2]; rw [← l2 X1 X1 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h53808 X1 X0]
    conv => enter [1]; rw [← l4 X2 X0 X1]
  have l6 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h53848 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X1 ◇ X2)) X3]
  have l7 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X2) X3]
  have l8 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [l9 X0 X3 X1 X2]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l10 X2 X2 X0 X1]
    conv => enter [1]; rw [l5 X2 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l11 X2 X3 X1 X0]
    conv => enter [1]; rw [← l2 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l12 x y x z]

theorem Equation4276_4343_4512_53820_53899_implies_Equation53824 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) (h53820 : Equation53820 G) (h53899 : Equation53899 G) : Equation53824 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [h4343 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X2 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h53899 X1 X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53820 X0 X1 X2]
    conv => enter [1]; rw [h4276 X0 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l2 X2 X1 X0]
    conv => enter [1]; rw [l3 X2 X1 X0 X3]
  intro x y z
  conv => enter [1]; rw [← l4 y x z x]

theorem Equation4276_4293_4512_53811_54201_implies_Equation53824 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) (h53811 : Equation53811 G) (h54201 : Equation54201 G) : Equation53824 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53811 X0 X1 X2]
    conv => enter [1]; rw [h4276 X0 X3]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54201 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X1)) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [← l0 X1 X2 X3 X0]
    conv => enter [1]; rw [h4293 X1 (X2 ◇ X3)]
  have l7 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X1))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l6 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ X1)]
  have l8 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l7 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X1]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X2 X1 X3]
    conv => enter [1]; rw [← l5 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l9 x y x z]

theorem Equation4343_4512_53820_53870_implies_Equation53824 (G : Type*) [Magma G] (h4343 : Equation4343 G) (h4512 : Equation4512 G) (h53820 : Equation53820 G) (h53870 : Equation53870 G) : Equation53824 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [h4343 (X1 ◇ X2) X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l1 X1 X2 X0]
    conv => enter [1, 2]; rw [← h53870 X1 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53820 X1 X2 X0]
    conv => enter [1]; rw [l2 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4276_4293_4512_53811_54172_implies_Equation53824 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) (h53811 : Equation53811 G) (h54172 : Equation54172 G) : Equation53824 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53811 X0 X1 X2]
    conv => enter [1]; rw [h4276 X0 X3]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X2 ◇ X3) ◇ ((X2 ◇ X3) ◇ X1)) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [← l0 X1 X2 X3 X0]
    conv => enter [1]; rw [h4293 X1 (X2 ◇ X3)]
  have l7 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X1))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l6 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ X1)]
  have l8 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l7 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X1]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
    conv => enter [1]; rw [l5 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l9 x y x z]

theorem Equation4276_4343_4512_53817_53899_implies_Equation53830 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h53899 : Equation53899 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4343 (X0 ◇ X1) sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h53899 X1 X0]
  have l2 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h53817 sK2 X1 X0]
    conv => enter [1]; rw [← l1 X0 X1 sK2]
  have l3 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l2 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l4 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [l3 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y x z]

theorem Equation4276_4293_4512_53817_54201_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h54201 : Equation54201 G) : Equation53834 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4293 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53817 X0 X1 X2]
    conv => enter [1]; rw [h4276 X0 X3]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54201 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← l1 X2 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l2 z x y x]
  conv => enter [1]; rw [l8 z x y]

theorem Equation4276_4343_4512_53817_53870_implies_Equation53830 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4343 : Equation4343 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h53870 : Equation53870 G) : Equation53830 G := by
  have l0 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h4343 (X0 ◇ X1) sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 sK2 : G, ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK2]
    conv => enter [1, 2]; rw [← h53870 X0 X1]
  have l2 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h53817 sK2 X0 X1]
    conv => enter [1]; rw [← l1 X0 X1 sK2]
  have l3 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l2 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l4 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [l3 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l4 x y x z]

theorem Equation4276_4293_4512_53817_54172_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4293 : Equation4293 G) (h4512 : Equation4512 G) (h53817 : Equation53817 G) (h54172 : Equation54172 G) : Equation53834 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4293 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53817 X0 X1 X2]
    conv => enter [1]; rw [h4276 X0 X3]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l3 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [← l5 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← l1 X2 X0 X1]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l8 X1 X2 X0]
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
  intro x y z
  conv => enter [1]; rw [← l9 y x z x]

theorem Equation4276_4321_4512_implies_Equation53855 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4321 : Equation4321 G) (h4512 : Equation4512 G) : Equation53855 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X1)) = ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h4321 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h4276 X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h4321 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [h4321 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X1)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X1]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X1) X2]
    conv => enter [1, 1]; rw [h4276 X1 X0]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [h4321 X1 X0]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4276 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h4321 X2 (X0 ◇ X1)]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l14 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l12 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l15 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l13 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l14 X0 X1 X2]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l15 X0 X2 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0 X1]
    conv => enter [1, 2]; rw [h4321 X1 X0]
  have l19 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X3))]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l19 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l21 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l20 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l22 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l17 X1 X2 X2]
    conv => enter [1, 2]; rw [h4276 X2 X0]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l18 X1 X0]
    conv => enter [1]; rw [h4321 (X0 ◇ (X1 ◇ X1)) X1]
  have l24 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l23 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X1]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l25 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l27 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l26 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l28 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1, 2, 2]; rw [← l10 X0 X1 X0]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1, 2]; rw [l16 X1 X0 X0]
  have l30 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4276 X0 X1]
    conv => enter [1]; rw [← l4 X1 X1]
    conv => enter [1, 2, 2]; rw [h4276 X1 X0]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1 X1]
    conv => enter [1]; rw [← l4 X1 X1]
    conv => enter [1, 2]; rw [l17 X1 X1 X0]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l16 X1 X0 (X0 ◇ X1)]
  have l33 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l16 X1 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l16 X1 X0 X1]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1]
    conv => enter [1]; rw [← l10 X0 X0 X1]
  have l36 : ∀ X2 X0 X1 : G, (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = ((X2 ◇ (X2 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4321 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [l22 X2 X0 X1]
  have l37 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l4 X2 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← l22 X0 (X1 ◇ (X1 ◇ X1)) X1]
  have l38 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [l22 X0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [l18 (X1 ◇ (X1 ◇ X1)) X2]
  have l39 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l38 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l40 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l37 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))]
  have l41 : ∀ X2 X0 X1 : G, (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = (X2 ◇ ((X2 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l36 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 (X2 ◇ X0) (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l42 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l39 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l43 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l40 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))]
  have l44 : ∀ X2 X0 X1 : G, (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l41 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l45 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l42 X1 X2 X0]
    conv => enter [1, 2]; rw [← l31 X1 X2]
  have l46 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l43 X2 X1 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l30 X0 X1]
  have l47 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X2 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l30 X0 X1]
    conv => enter [1]; rw [← l44 X2 X0 X1]
  have l48 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l31 X1 X2]
    conv => enter [1]; rw [← l45 X1 X2 X0]
  have l49 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l46 X2 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l30 X0 X1]
  have l50 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X2 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l47 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) X2]
  have l51 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l48 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))]
  have l52 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l49 X2 X1 X0]
    conv => enter [1]; rw [l34 X2 (X1 ◇ (X1 ◇ X1))]
  have l53 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l50 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X2]
  have l54 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l51 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))]
  have l55 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l52 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) (X2 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l56 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l54 X1 X2 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l30 X0 X1]
  have l57 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l55 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 (X2 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l58 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l56 X1 X2 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l30 X0 X1]
  have l59 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l57 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [l53 X1 X2 X1]
  have l60 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))))) := by
    intro X1 X2
    conv => enter [1]; rw [l58 X1 X2 X1]
    conv => enter [1]; rw [l59 X1 X2 X1]
  have l61 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h4276 X0 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l5 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1, 2]; rw [h4276 (X1 ◇ (X1 ◇ X1)) X0]
  have l62 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [← l5 X0 X2]
    conv => enter [1]; rw [l16 X0 X1 (X0 ◇ (X2 ◇ (X2 ◇ X2)))]
  have l63 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X2 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l22 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l64 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l63 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) (X2 ◇ (X2 ◇ X2))]
  have l65 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l61 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) (X0 ◇ (X0 ◇ X0))]
  have l66 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l64 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) (X2 ◇ (X2 ◇ X2))]
  have l67 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l65 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X0 ◇ (X0 ◇ X0))]
  have l68 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l66 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 (X2 ◇ (X2 ◇ X2))]
  have l69 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l67 X0 X1]
    conv => enter [1, 2]; rw [← l30 X1 X0]
  have l70 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l68 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l30 X1 X2]
  have l71 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l30 X1 X2]
    conv => enter [1]; rw [← l70 X0 X1 X2]
  have l72 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l71 X0 X1 X2]
    conv => enter [1]; rw [← l28 X0 X0]
  have l73 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [← l72 X0 X1 X2]
  have l74 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l35 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l75 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0 X0]
    conv => enter [1]; rw [l35 X0 X1]
  have l76 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l35 X0 X1]
    conv => enter [1]; rw [l16 X1 X0 (X0 ◇ X0)]
  have l77 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l35 X0 X1]
    conv => enter [1]; rw [h4321 (X1 ◇ (X0 ◇ X0)) X0]
  have l78 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l35 X0 X1]
    conv => enter [1]; rw [← l18 X0 (X0 ◇ (X1 ◇ X0))]
  have l79 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l78 X0 X1]
    conv => enter [1]; rw [l35 X0 (X0 ◇ (X1 ◇ X0))]
  have l80 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l77 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X0]
  have l81 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l73 X0 X1 X0]
    conv => enter [1]; rw [← l76 X1 X0]
  have l82 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l74 X2 X0 X1]
  have l83 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l79 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X0]
  have l84 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [← l80 X1 X0]
  have l85 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1 X0]
    conv => enter [1]; rw [← l81 X0 X1]
  have l86 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [← l83 X0 X1]
  have l87 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l84 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l88 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l86 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l89 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l87 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l90 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l88 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l91 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l60 X0 X1]
    conv => enter [1]; rw [← l89 X0 X1]
  have l92 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l90 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l93 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l73 X0 X1 X0]
    conv => enter [1]; rw [← l91 X0 X1]
  have l94 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l92 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l95 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l94 X0 X1]
    conv => enter [1, 2]; rw [l21 X1 X0 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l96 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l93 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l95 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l93 X0 (X1 ◇ (X0 ◇ X0))]
  have l97 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ (X2 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [l17 X0 X1 X2]
    conv => enter [1]; rw [l10 (X2 ◇ X1) X2 X2]
  have l98 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) = (X2 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 (X2 ◇ X2)]
    conv => enter [1, 2, 2, 2]; rw [h4276 X2 X0]
  have l99 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1, 2]; rw [l10 X2 X0 X1]
  have l100 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l22 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 2]; rw [← l10 X0 X1 X1]
  have l101 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [l16 X2 X1 (X0 ◇ (X1 ◇ X2))]
  have l102 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X2 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l10 X1 X1 X0]
    conv => enter [1]; rw [← l100 X0 X1 X2]
  have l103 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X2 ◇ X2) ◇ X1))) = (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l98 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X2 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l104 : ∀ X2 X1 X0 : G, ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l97 X2 X1 X0]
    conv => enter [1]; rw [l82 X2 X2 (X2 ◇ X1)]
  have l105 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l102 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X2 ◇ (X2 ◇ X2))]
  have l106 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) = (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X2 X2 X1]
    conv => enter [1]; rw [l103 X1 X2 X0]
  have l107 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X2 ◇ X2))) = ((X2 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l93 X2 ((X2 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [← l104 X2 X1 X0]
  have l108 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l105 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ (X2 ◇ X2))]
  have l109 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X2 ◇ X1))) = (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l31 X2 X1]
    conv => enter [1]; rw [l106 X1 X2 X0]
  have l110 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X2 ◇ X2))) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l107 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X2 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l111 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l108 X1 X0 X2]
    conv => enter [1, 2]; rw [← l30 X1 X2]
  have l112 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [l31 X0 X1]
    conv => enter [1]; rw [← l110 X2 X1 X0]
  have l113 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l69 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l114 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l69 X0 X1]
    conv => enter [1]; rw [l17 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l115 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l69 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X0))) X2]
  have l116 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l10 (X1 ◇ (X0 ◇ (X0 ◇ X0))) X2 X1]
    conv => enter [1, 2, 2]; rw [← l69 X0 X1]
  have l117 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)))) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l116 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l118 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l115 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l119 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l114 X1 X0 X2]
    conv => enter [1, 2]; rw [← l30 X2 X0]
  have l120 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l113 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l121 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)))) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l117 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l122 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l118 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l123 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l69 X0 X0]
    conv => enter [1]; rw [← l119 X1 X0 X0]
  have l124 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l34 X1 X0]
    conv => enter [1]; rw [l120 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l34 X1 X0]
  have l125 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l121 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l126 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l122 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 X2]
  have l127 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l34 X0 X1]
    conv => enter [1]; rw [l124 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [l34 X0 X1]
  have l128 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X2 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l125 X2 X1 X0]
    conv => enter [1, 2]; rw [← l109 X0 X2 X0]
  have l129 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X2 ◇ X1))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l128 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) (X2 ◇ X1)]
  have l130 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X2 ◇ X1)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l129 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) (X2 ◇ X1)]
  have l131 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l130 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 (X2 ◇ X1)]
  have l132 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X1))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l131 X1 X0 X2]
    conv => enter [1, 2]; rw [← l126 X0 (X2 ◇ X1) X1]
  have l133 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l11 X2 X0 X1]
    conv => enter [1, 2]; rw [l4 X1 X0]
  have l134 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l11 X2 X0 X1]
    conv => enter [1]; rw [l10 X2 X2 X2]
    conv => enter [1, 2, 2]; rw [l11 X2 X0 X1]
  have l135 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l16 X3 X2 (X2 ◇ X2)]
    conv => enter [1, 2, 2]; rw [l11 X2 X0 X1]
  have l136 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l35 (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) X2]
    conv => enter [1, 2, 2]; rw [← l11 X0 X2 X1]
  have l137 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l136 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X2 ◇ X1))) ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l138 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l135 X3 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l34 X1 X0]
  have l139 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l34 X1 X0]
    conv => enter [1]; rw [l134 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [l34 X1 X0]
  have l140 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l137 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X2 ◇ X1)) ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l141 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l138 X3 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l34 X0 X1]
  have l142 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l34 X0 X1]
    conv => enter [1]; rw [l139 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [l34 X0 X1]
  have l143 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l140 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l144 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l127 X0 X1 X2]
    conv => enter [1]; rw [← l142 X2 X0 X1]
  have l145 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l143 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X1 ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l146 : ∀ X1 X2 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l145 X1 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l73 X1 (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) X1]
  have l147 : ∀ X1 X2 : G, ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))))) := by
    intro X1 X2
    conv => enter [1]; rw [l146 X1 X2]
    conv => enter [1, 2]; rw [← l62 X1 X2 X1]
  have l148 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l96 X1 X2]
    conv => enter [1]; rw [← l147 X1 X2]
  have l149 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l148 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X2 ◇ X1))) (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))]
  have l150 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l149 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X2 ◇ X1)) (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))]
  have l151 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l150 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))]
  have l152 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l151 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X1 (X2 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))))]
  have l153 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1)))))))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l152 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X2 ◇ X1))) (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X1))))]
  have l154 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l153 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← l141 X2 X1 X1 (X2 ◇ (X1 ◇ (X2 ◇ X1)))]
  have l155 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1))))))) := by
    intro X1 X2
    conv => enter [1]; rw [l154 X1 X2]
    conv => enter [1, 2, 2]; rw [l21 X1 X2 X2 (X1 ◇ X1)]
  have l156 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))))) := by
    intro X1 X2
    conv => enter [1]; rw [l155 X1 X2]
    conv => enter [1]; rw [l21 X1 X2 X2 (X2 ◇ (X1 ◇ X1))]
  have l157 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1))))) := by
    intro X1 X2
    conv => enter [1]; rw [l156 X1 X2]
    conv => enter [1, 2]; rw [← l132 X1 X2 X1]
  have l158 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X1 X2
    conv => enter [1]; rw [l157 X1 X2]
    conv => enter [1]; rw [← l101 X1 X2 X2]
  have l159 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X2
    conv => enter [1]; rw [l158 X1 X2]
    conv => enter [1]; rw [← l10 X2 X1 X2]
  have l160 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X2
    conv => enter [1]; rw [l123 X1 X1]
    conv => enter [1]; rw [l159 X1 X2]
  have l161 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l133 X2 X0 X1]
    conv => enter [1]; rw [l10 X2 X2 X2]
    conv => enter [1, 2, 2]; rw [l133 X2 X0 X1]
  have l162 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))) = ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l10 (X2 ◇ X2) X3 X2]
    conv => enter [1, 2, 2]; rw [l133 X2 X0 X1]
  have l163 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l162 X3 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 X2 (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
  have l164 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X2 X2 (X3 ◇ X2)]
    conv => enter [1]; rw [l163 X3 X2 X0 X1]
  have l165 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X3)))) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l132 X2 X2 X3]
    conv => enter [1]; rw [l164 X3 X2 X0 X1]
  have l166 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ X2))) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l112 X2 X2 X3]
    conv => enter [1]; rw [l165 X2 X3 X0 X1]
  have l167 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l160 X2 X2]
    conv => enter [1]; rw [l166 X2 X3 X0 X1]
  have l168 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)))) = ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l10 (X0 ◇ (X1 ◇ X1)) X2 X1]
    conv => enter [1, 2, 2]; rw [l29 X1 X0]
  have l169 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)))) = (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l168 X2 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
  have l170 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l169 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
  have l171 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l167 X1 X2 X0 X1]
    conv => enter [1]; rw [← l170 X2 X1 X0]
  have l172 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l171 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) (X2 ◇ X1)]
  have l173 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l172 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 (X2 ◇ X1)]
  have l174 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l123 X1 X0]
    conv => enter [1]; rw [l173 X0 X1 X2]
  have l175 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [← l34 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2]
  have l176 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [← l34 X0 X1]
    conv => enter [1]; rw [l10 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2 X0]
  have l177 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ X0))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l176 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) (X2 ◇ X0)]
  have l178 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l175 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l179 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l177 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X2 ◇ X0)]
  have l180 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l178 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l181 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l179 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X0 (X2 ◇ X0)]
  have l182 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l180 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l183 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X0)) (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l181 X1 X0 X2]
  have l184 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1]; rw [l182 X0 X1 X2]
  have l185 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l183 X1 X0 X2]
  have l186 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l184 X0 X1 X2]
  have l187 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l185 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l188 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l186 X0 X1 X2]
  have l189 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0))))))) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [l144 X0 X1 X2]
    conv => enter [1]; rw [← l187 X2 X0 X1]
  have l190 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l189 X1 X0 X2]
    conv => enter [1, 2]; rw [← l188 X0 X1 (X2 ◇ X0)]
  have l191 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l33 X1 X0 X0]
    conv => enter [1]; rw [l190 X1 X0 X2]
  have l192 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l161 X1 X0 X1]
    conv => enter [1]; rw [l191 X1 X0 X2]
  have l193 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l21 X1 X0 X0 X0]
    conv => enter [1]; rw [l192 X1 X0 X2]
  have l194 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l73 X0 X1 X0]
    conv => enter [1]; rw [l193 X0 X1 X2]
  have l195 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l160 X0 X0]
    conv => enter [1]; rw [l194 X0 X2 X1]
  have l196 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) = (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l144 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X3]
  have l197 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) = (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
    conv => enter [1]; rw [l196 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
  have l198 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X3]
    conv => enter [1]; rw [l197 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l199 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l198 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l200 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l10 X2 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1, 2, 2, 2]; rw [l75 X1 X0]
  have l201 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l200 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
  have l202 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l201 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
  have l203 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [l174 X0 X1 X2]
    conv => enter [1]; rw [← l202 X2 X1 X0]
  have l204 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l203 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l205 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l204 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l206 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l199 X1 X0 X2 X2]
    conv => enter [1]; rw [← l205 X1 X0 X2]
  have l207 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l111 X0 X1 X0]
    conv => enter [1]; rw [← l206 X1 X0 X2]
  have l208 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l85 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X2]
  have l209 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l208 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l210 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l209 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l211 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l207 X0 X0 X2]
    conv => enter [1]; rw [← l210 X0 X1 X2]
  have l212 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l211 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
  have l213 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l212 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l214 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l213 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l215 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l160 X0 X0]
    conv => enter [1]; rw [l214 X0 X1 X2]
  have l216 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l99 X0 X1 X2]
    conv => enter [1]; rw [← l10 X1 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1)))]
  have l217 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [l99 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
  have l218 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l217 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1))) X3]
  have l219 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l216 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X1)) X1]
  have l220 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l218 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X1)) X3]
  have l221 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l219 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) X1]
  have l222 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l220 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) X3]
  have l223 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l221 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X1]
  have l224 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l222 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l225 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ X1)) (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l223 X0 X1 X2]
  have l226 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1]; rw [l224 X0 X1 X2 X3]
  have l227 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X2 (X0 ◇ X1) (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l225 X0 X1 X2]
  have l228 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X0) X3]
    conv => enter [1]; rw [l226 X0 X1 X2 X3]
  have l229 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l227 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
  have l230 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 X0 X3]
    conv => enter [1]; rw [l228 X0 X1 X2 X3]
  have l231 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l195 X0 X2 X1]
    conv => enter [1]; rw [← l229 X1 X0 X2]
  have l232 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l230 X0 X1 X2 X1]
    conv => enter [1]; rw [← l231 X0 X1 X2]
  have l233 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l215 X0 X1 X0]
    conv => enter [1]; rw [← l232 X0 X1 X2]
  have l234 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l233 X0 X2 X1]
    conv => enter [1]; rw [← l10 X1 X0 X2]
  intro x y z w
  conv => enter [1]; rw [h4276 x z]
  conv => enter [1]; rw [l234 z y w]

theorem Equation4276_4314_4512_implies_Equation53844 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4314 : Equation4314 G) (h4512 : Equation4512 G) : Equation53844 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [← h4314 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [h4314 X0 X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4276 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4314 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h4314 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4314 X1 (X0 ◇ X1)]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X1]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4314 X0 X1]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X1]
    conv => enter [1]; rw [l6 X0 X1 X0]
  have l12 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X3 ◇ (X4 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [← l11 X0 X0 X1]
    conv => enter [1]; rw [l11 X0 X3 X4]
  have l13 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X2))) = (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l6 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4314 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2 X2]
    conv => enter [1]; rw [← l2 X2 X2]
    conv => enter [1, 2]; rw [l12 X2 X2 X0 X1]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l7 X2 X0 X1]
    conv => enter [1, 2]; rw [l13 X0 X1 X2]
  have l16 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [l14 X1 X2 X0]
    conv => enter [1]; rw [← l15 X2 X0 X1]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l14 X1 X2 X2]
    conv => enter [1]; rw [l16 X2 X1 X0]
  intro x y z
  conv => enter [1]; rw [l11 x x y]
  conv => enter [1]; rw [l17 x y z]
  conv => enter [1, 2]; rw [← h4314 z x]

theorem Equation4276_4291_4512_implies_Equation53827 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4291 : Equation4291 G) (h4512 : Equation4512 G) : Equation53827 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← h4291 X1 X0]
    conv => enter [1]; rw [h4291 X1 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [h4291 X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4291 (X1 ◇ X2) X0]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← h4291 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4291 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X1 ◇ X2))]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4291 X0 (X1 ◇ X0)]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4276 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X1 ◇ X2))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← l5 X2 X2 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← l3 X2 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l11 X2 X1 X0]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l7 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X3))]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ X3))]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l14 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X3)]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l17 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [← l12 X1 (X1 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 2, 2]; rw [← l7 X0 X1 X2]
  have l18 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [l17 X3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4291 X0 (X1 ◇ (X0 ◇ X2))]
  have l19 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l18 X3 X1 X0 X2]
    conv => enter [1]; rw [← l16 X0 X1 X0 X2]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [l5 X2 X0 X1]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2]
    conv => enter [1]; rw [← l15 X1 X1 X0 X2]
  have l22 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← l19 X3 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l22 x y z x]
  conv => enter [1]; rw [← l7 y x z]

theorem Equation4290_4512_53840_implies_Equation53823 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4512 : Equation4512 G) (h53840 : Equation53840 G) : Equation53823 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4290 X0 X1]
    conv => enter [1]; rw [h4290 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l0 X1 X0]
  intro x y
  conv => enter [1]; rw [h53840 x x y]
  conv => enter [1]; rw [l1 x y]

theorem Equation4290_4512_53842_implies_Equation53824 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4512 : Equation4512 G) (h53842 : Equation53842 G) : Equation53824 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h4290 X0 X1]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4290 X0 (X1 ◇ X2)]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53842 X0 X1 X2]
    conv => enter [1]; rw [l1 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [← l4 y x z]

theorem Equation4276_4290_4512_53842_implies_Equation53834 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) (h53842 : Equation53842 G) : Equation53834 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) X2]
    conv => enter [1, 1]; rw [← h4290 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53842 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4290 X0 X1]
  intro x y z
  conv => enter [1]; rw [h4276 x y]
  conv => enter [1]; rw [l4 y x z]
  conv => enter [1]; rw [← l3 y x z]

theorem Equation4290_4512_53811_implies_Equation53824 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h4512 : Equation4512 G) (h53811 : Equation53811 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53811 sK0 X0 X1]
    conv => enter [1]; rw [h4290 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4290 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4276_4290_4512_53811_implies_Equation53830 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4290 : Equation4290 G) (h4512 : Equation4512 G) (h53811 : Equation53811 G) : Equation53830 G := by
  have l0 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h53811 sK2 X0 X1]
    conv => enter [1]; rw [h4290 sK2 (X0 ◇ X1)]
  have l1 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK2)]
  have l2 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l2 x y x z]

theorem Equation4290_53850_implies_Equation53830 (G : Type*) [Magma G] (h4290 : Equation4290 G) (h53850 : Equation53850 G) : Equation53830 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53850 X0 X2 X1]
    conv => enter [1, 2]; rw [h4290 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4369_4512_53848_implies_Equation53840 (G : Type*) [Magma G] (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53840 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4369 X0 X1 X2]
    conv => enter [1]; rw [h4369 X3 X2 (X1 ◇ X0)]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X3)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X0 X1 X1]
    conv => enter [1]; rw [← h53848 X2 X1 X0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

theorem Equation4276_4369_4512_53815_implies_Equation53848 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53815 : Equation53815 G) : Equation53848 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4369 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53815 X0 X1]
    conv => enter [1]; rw [← l0 X0 X1 X0 X1]
  intro x y z
  conv => enter [1]; rw [h4276 x y]
  conv => enter [1]; rw [l1 y z]

theorem Equation4276_4369_4512_53828_implies_Equation53827 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53828 : Equation53828 G) : Equation53827 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X2 ◇ X0) ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53828 X0 X1 X2]
    conv => enter [1]; rw [h4369 X1 X0 (X2 ◇ X0)]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X2 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X2) ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [h4369 X1 X0 (X0 ◇ X2)]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [h4276 x y]
  conv => enter [1]; rw [l3 y x z]

theorem Equation4369_4512_53828_implies_Equation53824 (G : Type*) [Magma G] (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53828 : Equation53828 G) : Equation53824 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = ((X1 ◇ X0) ◇ (X2 ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4369 X0 X1 X2]
    conv => enter [1]; rw [h4369 X3 X2 (X1 ◇ X0)]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4369 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ X3)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53828 X0 X1 X2]
    conv => enter [1]; rw [← l3 X0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]
  conv => enter [1]; rw [l5 x x y z]

theorem Equation4276_4369_4512_53844_implies_Equation53855 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53844 : Equation53844 G) : Equation53855 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [h4369 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X3) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ X3)) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ X2) ◇ (X2 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53844 X0 X1 X2]
    conv => enter [1]; rw [h4369 X1 X2 (X0 ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X2 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 X2 (X2 ◇ X1)]
  intro x y z w
  conv => enter [1]; rw [h4276 x w]
  conv => enter [1]; rw [l5 w y z]
  conv => enter [1]; rw [l3 w y y z]
  conv => enter [1, 2]; rw [h4369 y w z]

theorem Equation4276_4369_4512_53814_implies_Equation53844 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53814 : Equation53814 G) : Equation53844 G := by
  have l0 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ ((sK0 ◇ X0) ◇ X1)) = ((X0 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4369 sK2 sK0 X0]
  have l1 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) = (sK2 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK2) X1]
    conv => enter [1]; rw [← l0 sK2 sK0 X0 X1]
  have l2 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) = (sK2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l1 X0 sK0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l3 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) = ((X0 ◇ X1) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l2 X0 sK0 sK2 X1]
    conv => enter [1]; rw [h4369 sK2 sK0 (X0 ◇ X1)]
  have l4 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ ((sK0 ◇ sK2) ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l3 X0 sK0 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) = (X0 ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [h4369 sK2 (sK0 ◇ sK2) X0]
  have l6 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← l4 X0 sK0 sK2 sK2]
    conv => enter [1]; rw [← l5 sK2 sK0 X0]
  have l7 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 X0]
    conv => enter [1]; rw [← h53814 sK2 sK0 X0]
  have l8 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4276 sK0 sK2]
    conv => enter [1]; rw [← l7 sK2 sK0 X0]
  have l9 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l8 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) X0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4369_4512_53855_implies_Equation53827 (G : Type*) [Magma G] (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53855 : Equation53855 G) : Equation53827 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4369 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = ((X3 ◇ X1) ◇ (X2 ◇ X1)) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h53855 X0 X1 X2 X3]
    conv => enter [1]; rw [h4369 X1 X2 (X3 ◇ X1)]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1]; rw [← h4512 X3 X1 (X2 ◇ X1)]
  have l3 : ∀ X0 X3 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X3 ◇ X2) ◇ (X2 ◇ X1)) := by
    intro X0 X3 X2 X1
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1]; rw [h4369 X1 X2 (X3 ◇ X2)]
  have l4 : ∀ X0 X3 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X3 ◇ (X2 ◇ (X2 ◇ X1))) := by
    intro X0 X3 X2 X1
    conv => enter [1]; rw [l3 X0 X3 X2 X1]
    conv => enter [1]; rw [← h4512 X3 X2 (X2 ◇ X1)]
  have l5 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4369 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X3 X2]
  intro x y z
  conv => enter [1]; rw [l4 x x y z]
  conv => enter [1]; rw [← l5 y x y z]

theorem Equation4369_4512_53850_implies_Equation53827 (G : Type*) [Magma G] (h4369 : Equation4369 G) (h4512 : Equation4512 G) (h53850 : Equation53850 G) : Equation53827 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X2 ◇ X0) ◇ (X2 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53850 X0 X1 X2]
    conv => enter [1]; rw [h4369 X1 X2 (X2 ◇ X0)]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X2 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X2 X0 (X2 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4276_4284_4512_implies_Equation53840 (G : Type*) [Magma G] (h4276 : Equation4276 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) : Equation53840 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h4284 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4284 (sK2 ◇ sK2) X0]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← h4284 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) ((sK2 ◇ sK2) ◇ sK2)]
  have l6 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h4284 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ X0)]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4284 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l6 sK1 sK2 X0]
    conv => enter [1]; rw [← l3 sK1 (sK2 ◇ sK2) X0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4284 sK1 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l10 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l4 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ X0)]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← l8 sK1 sK2 X0]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l11 sK1 sK2 X0]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 sK2 sK2]
  have l14 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 sK2]
    conv => enter [1]; rw [← l12 sK1 sK2 sK2]
  have l15 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4284 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2 X0]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4276 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l15 sK1 sK2]
  have l18 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [h4284 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
  have l19 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2 sK2]
    conv => enter [1]; rw [l19 sK1 sK2]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2]
  have l22 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4284 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l19 sK1 sK2]
  have l23 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l21 sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [← l21 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation4275_4512_53807_implies_Equation53913 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation53913 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [h4275 sK1 X0]
  have l1 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h4275 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK2 sK1 sK0]
    conv => enter [1]; rw [h4275 (sK2 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4275 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK1 sK1]
  have l4 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4275 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [h53807 sK1]
    conv => enter [1, 2]; rw [h4275 sK1 sK0]
  have l6 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK2 sK1 sK0]
    conv => enter [1]; rw [h53807 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK2 sK1 sK0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l2 sK2 sK1 sK1 sK1]
    conv => enter [1]; rw [l6 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l2 sK2 sK1 sK1 sK1]
  have l8 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK1 sK1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l9 sK2 sK1 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l2 sK2 sK0 sK1 sK1]
    conv => enter [1]; rw [l8 sK2 sK0 sK1]
  have l12 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 sK2]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← l12 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4270_4512_53807_implies_Equation54181 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h53807 : Equation53807 G) : Equation54181 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [← h4270 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4270 sK0 sK2]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4270 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53807 sK0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l6 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2 X0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l3 sK0 sK2]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4270 sK0 sK2]
    conv => enter [1]; rw [l8 sK0 sK2]
  have l10 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l3 sK0 sK2]
    conv => enter [1]; rw [← h4270 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l11 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l0 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 sK2]
  have l12 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l11 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l9 sK0 sK2]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [← l6 sK0 sK2 (sK0 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK2 ◇ sK2)) sK0 sK2]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [l14 sK0 sK2]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4270 sK0 sK2]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l17 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53807 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK2 ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l22 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 (sK0 ◇ (sK2 ◇ sK2)) sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l24 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l23 sK0 sK2 sK1]
    conv => enter [1]; rw [← l18 sK0 sK2 (sK1 ◇ (sK0 ◇ sK0)) sK1]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
  have l26 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK0 sK2 sK1]
    conv => enter [1]; rw [l6 sK0 sK2 (sK1 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l26 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 sK1]
    conv => enter [1]; rw [l27 sK1 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l30 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [← l30 sK0 sK0 sK1]
  have l32 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1, 2]; rw [h4270 sK0 sK2]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0 sK1]
    conv => enter [1]; rw [← l32 sK1 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l35 x z y]

theorem Equation4275_53900_implies_Equation53921 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53900 : Equation53900 G) : Equation53921 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4275 X1 X0]
    conv => enter [1]; rw [h4275 X1 X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h4275 X0 X1]
    conv => enter [1]; rw [h53900 X1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y y]
  conv => enter [1]; rw [l1 y z]

theorem Equation4270_54164_implies_Equation54167 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54164 : Equation54164 G) : Equation54167 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h4270 X0 X1]
    conv => enter [1]; rw [h54164 X0 X1]
  intro x y z
  conv => enter [1]; rw [← h4270 x y]
  conv => enter [1]; rw [l0 x z]

theorem Equation4275_53870_implies_Equation53959 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53870 : Equation53870 G) : Equation53959 G := by
  intro x y z
  conv => enter [1]; rw [← h4275 y x]
  conv => enter [1]; rw [h4275 y z]
  conv => enter [1]; rw [h53870 z y]

theorem Equation4270_54172_implies_Equation54183 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54172 : Equation54172 G) : Equation54183 G := by
  intro x y z
  conv => enter [1]; rw [← h4270 x y]
  conv => enter [1]; rw [h4270 x z]
  conv => enter [1]; rw [h54172 x z]

theorem Equation4275_4512_53825_implies_Equation53959 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h4512 : Equation4512 G) (h53825 : Equation53825 G) : Equation53959 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53825 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [← l1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4270_4512_53813_implies_Equation54183 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h4512 : Equation4512 G) (h53813 : Equation53813 G) : Equation54183 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK2]
  have l1 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53813 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK2 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l6 x z y]

theorem Equation53951_53959_implies_Equation53963 (G : Type*) [Magma G] (h53951 : Equation53951 G) (h53959 : Equation53959 G) : Equation53963 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53959 X0 X1 X2]
    conv => enter [1]; rw [← h53951 X2 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h53951 w y z]

theorem Equation54173_54183_implies_Equation54184 (G : Type*) [Magma G] (h54173 : Equation54173 G) (h54183 : Equation54183 G) : Equation54184 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54173 X0 X1 X1]
    conv => enter [1]; rw [← h54183 X0 X2 X1]
  intro x y z w
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h54173 x z w]

theorem Equation53876_53959_implies_Equation53963 (G : Type*) [Magma G] (h53876 : Equation53876 G) (h53959 : Equation53959 G) : Equation53963 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53959 X0 X1 X2]
    conv => enter [1]; rw [← h53876 X2 X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X1))) = (X3 ◇ (X3 ◇ X1)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53876 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X3]
  intro x y z w
  conv => enter [1]; rw [← l1 z y w x]

theorem Equation4270_54182_54183_implies_Equation54184 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54182 : Equation54182 G) (h54183 : Equation54183 G) : Equation54184 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54182 X0 X1 X1]
    conv => enter [1]; rw [← h54183 X0 X2 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4270 X0 X2]
    conv => enter [1]; rw [h54182 X0 X2 X1]
  intro x y z w
  conv => enter [1]; rw [l0 x y x]
  conv => enter [1]; rw [l1 x z w]

theorem Equation4275_53828_implies_Equation53963 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53828 : Equation53828 G) : Equation53963 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4275 sK2 sK1]
    conv => enter [1]; rw [h53828 sK2 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation4270_53814_implies_Equation54184 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h53814 : Equation53814 G) : Equation54184 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 sK3 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK0 X0 sK3
    conv => enter [1]; rw [l0 sK1 sK0 sK1]
    conv => enter [1]; rw [h53814 sK1 X0 sK3]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4275_53812_implies_Equation53921 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53812 : Equation53812 G) : Equation53921 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [h53812 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4270_53809_implies_Equation54167 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h53809 : Equation53809 G) : Equation54167 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53809 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation4275_53917_implies_Equation53903 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53917 : Equation53917 G) : Equation53903 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4275 X1 X0]
    conv => enter [1]; rw [h4275 X1 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4275 X0 X2]
    conv => enter [1]; rw [h53917 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y y]
  conv => enter [1]; rw [l1 y x z]

theorem Equation4270_54177_implies_Equation54185 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54177 : Equation54177 G) : Equation54185 G := by
  intro x y z
  conv => enter [1]; rw [← h4270 x y]
  conv => enter [1]; rw [h4270 x z]
  conv => enter [1]; rw [h54177 x z y]

theorem Equation4275_53884_implies_Equation53938 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53884 : Equation53884 G) : Equation53938 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4275 X1 X0]
    conv => enter [1]; rw [h4275 X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X3 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53884 X0 X2 X1]
    conv => enter [1]; rw [l0 X0 X2 X3]
  intro x y z
  conv => enter [1]; rw [← l1 z x y x]

theorem Equation4270_54168_implies_Equation54166 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54168 : Equation54168 G) : Equation54166 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4270 X0 X2]
    conv => enter [1]; rw [h54168 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [← h4270 x y]
  conv => enter [1]; rw [l0 x y z]

theorem Equation4275_4512_53838_53842_53934_implies_Equation53938 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h4512 : Equation4512 G) (h53838 : Equation53838 G) (h53842 : Equation53842 G) (h53934 : Equation53934 G) : Equation53938 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4275 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [← h4275 X0 sK1]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53934 X0 X0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4275 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h4275 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4275 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53934 X0 X0 sK0]
    conv => enter [1]; rw [l7 sK0 X0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4275 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK1 X0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4275 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l15 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4275 sK1 sK0]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l23 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4275 sK1 X0]
  have l24 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [← h4275 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h4275 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l26 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l24 X0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l27 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53934 X0 sK1 sK1]
    conv => enter [1]; rw [← l23 sK1 X0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l26 X0 sK1 sK0]
  have l29 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l27 X0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 sK1]
  have l30 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l29 X0 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK1 sK1]
  have l31 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4275 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l35 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2]; rw [h53838 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (X1 ◇ X0))]
  have l37 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l36 sK0 X0 sK1 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 (X1 ◇ X0)]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53838 (sK0 ◇ sK1) sK0 sK0]
  have l39 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h53934 X0 X0 sK0]
    conv => enter [1]; rw [l37 sK0 X0 sK1 X1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK0 sK1]
  have l41 : ∀ sK1 X0 sK0 X1 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [← l25 X0 sK1]
    conv => enter [1]; rw [l39 X0 sK0 sK1 X1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ sK1)]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l43 sK0 sK1 X0]
    conv => enter [1]; rw [← l41 sK1 X0 sK0 (sK0 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1 sK1]
  have l47 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53842 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l48 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l47 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l49 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l48 sK1 X0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l50 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l49 X0 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1 sK1]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l50 X0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l51 x y z]

theorem Equation4270_53811_implies_Equation54166 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h53811 : Equation53811 G) : Equation54166 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK1]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1]; rw [h53811 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation53880_53959_implies_Equation53942 (G : Type*) [Magma G] (h53880 : Equation53880 G) (h53959 : Equation53959 G) : Equation53942 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53959 X0 X1 X2]
    conv => enter [1]; rw [← h53880 X2 X1 X1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h53880 z y x]

theorem Equation4270_54178_implies_Equation54187 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54178 : Equation54178 G) : Equation54187 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK1]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1]; rw [h54178 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4275_53846_implies_Equation53942 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53846 : Equation53846 G) : Equation53942 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4275 sK1 sK2]
    conv => enter [1]; rw [h4275 sK1 X0]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4275 sK1 sK2]
    conv => enter [1]; rw [h53846 sK1 sK2 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z x]

theorem Equation4270_53819_implies_Equation54187 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h53819 : Equation53819 G) : Equation54187 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK1]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 X0]
    conv => enter [1]; rw [h53819 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4275_53818_implies_Equation53903 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53818 : Equation53818 G) : Equation53903 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4275 sK1 sK2]
    conv => enter [1]; rw [h4275 sK1 X0]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4275 sK1 sK2]
    conv => enter [1]; rw [h53818 sK1 X0 sK2]
  have l2 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y x z]

theorem Equation4270_53818_implies_Equation54185 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h53818 : Equation53818 G) : Equation54185 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h53818 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation53876_53959_53985_implies_Equation53946 (G : Type*) [Magma G] (h53876 : Equation53876 G) (h53959 : Equation53959 G) (h53985 : Equation53985 G) : Equation53946 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53959 X0 X1 X2]
    conv => enter [1]; rw [← h53876 X2 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h53985 w y z x]

theorem Equation4270_54180_implies_Equation54188 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h54180 : Equation54180 G) : Equation54188 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [← h4270 X0 X1]
    conv => enter [1]; rw [h4270 X0 sK2]
  have l1 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [l0 X0 sK2 X1]
    conv => enter [1]; rw [h54180 X0 X1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation53892_53942_implies_Equation53946 (G : Type*) [Magma G] (h53892 : Equation53892 G) (h53942 : Equation53942 G) : Equation53946 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53942 X0 X1 X2]
    conv => enter [1]; rw [← h53892 X2 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X4 ◇ (X4 ◇ X3)) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← h53892 X0 X3 X1 X2]
    conv => enter [1]; rw [l0 X0 X3 X4]
  intro x y z w
  conv => enter [1]; rw [← l1 z x w y x]

theorem Equation54179_54194_implies_Equation54188 (G : Type*) [Magma G] (h54179 : Equation54179 G) (h54194 : Equation54194 G) : Equation54188 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54179 X0 X1 X2]
    conv => enter [1]; rw [← h54194 X0 X2 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1]; rw [h54194 x w z y]

theorem Equation4275_53854_implies_Equation53946 (G : Type*) [Magma G] (h4275 : Equation4275 G) (h53854 : Equation53854 G) : Equation53946 G := by
  have l0 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4275 sK2 sK0]
    conv => enter [1]; rw [h4275 sK2 X0]
  have l1 : ∀ sK0 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4275 sK2 sK0]
    conv => enter [1]; rw [h53854 sK2 X0 X1 sK0]
  have l2 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 sK0 sK2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l2 x y z x w]

theorem Equation4270_53821_implies_Equation54188 (G : Type*) [Magma G] (h4270 : Equation4270 G) (h53821 : Equation53821 G) : Equation54188 G := by
  have l0 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [← h4270 X0 sK2]
    conv => enter [1]; rw [h53821 X0 X1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

end Semigroup5
