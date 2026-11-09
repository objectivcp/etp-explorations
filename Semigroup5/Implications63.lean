import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54179_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54179 : Equation54179 G) : Equation53808 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1) X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l7 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54179 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54179 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54179 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l16 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54179 X0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54179 X0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 (sK0 ◇ sK1)]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54179 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l17 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h54179 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h54179 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1) sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ sK0)]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 sK0 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l30 sK0 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l31 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [h54179 (sK0 ◇ sK0) X0 sK0]
  have l35 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l22 sK0 X0]
  have l36 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l35 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l16 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ sK0)]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l42 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ sK1)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 (sK0 ◇ sK1) sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1 sK1]
    conv => enter [1]; rw [← l48 sK0 sK1]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l8 sK0]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l53 x y]

@[equational_result]
theorem Equation53968_implies_Equation53934 (G : Type*) [Magma G] (h53968 : Equation53968 G) : Equation53934 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53968 sK0 sK1 X0]
    conv => enter [1]; rw [h53968 X0 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h53968 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation4512_53968_implies_Equation53907 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53968 : Equation53968 G) : Equation53907 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53968 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h53968 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h53968 X0 (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← h53968 sK1 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53968 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation53968_implies_Equation53832 (G : Type*) [Magma G] (h53968 : Equation53968 G) : Equation53832 G := by
  intro x y
  conv => enter [1]; rw [h53968 x x y]

theorem Equation4512_53968_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53968 : Equation53968 G) : Equation53822 G := by
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
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l6 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h53968 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l10 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ X0)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ X0)]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l13 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53968 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l19 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l21 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l23 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l27 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l28 sK0]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l29 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l31 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l32 sK0]
    conv => enter [1]; rw [← l11 sK1 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l27 sK0]
    conv => enter [1]; rw [h53968 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l27 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53968 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l11 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [← l33 sK1 sK0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l34 sK0 X0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h53968 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 2, 2]; rw [← l40 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK0]
    conv => enter [1]; rw [← l41 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l42 x y]

@[equational_result]
theorem Equation54178_implies_Equation54172 (G : Type*) [Magma G] (h54178 : Equation54178 G) : Equation54172 G := by
  intro x y
  conv => enter [1]; rw [h54178 x y x]

@[equational_result]
theorem Equation54178_implies_Equation54175 (G : Type*) [Magma G] (h54178 : Equation54178 G) : Equation54175 G := by
  intro x y
  conv => enter [1]; rw [h54178 x y y]

@[equational_result]
theorem Equation54178_implies_Equation53809 (G : Type*) [Magma G] (h54178 : Equation54178 G) : Equation53809 G := by
  intro x y
  conv => enter [1]; rw [h54178 x x y]

@[equational_result]
theorem Equation53880_implies_Equation53870 (G : Type*) [Magma G] (h53880 : Equation53880 G) : Equation53870 G := by
  intro x y
  conv => enter [1]; rw [h53880 x y y]

@[equational_result]
theorem Equation53880_implies_Equation53860 (G : Type*) [Magma G] (h53880 : Equation53880 G) : Equation53860 G := by
  intro x y
  conv => enter [1]; rw [h53880 x y x]

@[equational_result]
theorem Equation53880_implies_Equation53812 (G : Type*) [Magma G] (h53880 : Equation53880 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h53880 x x y]

theorem Equation4512_54177_implies_Equation54179 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54177 : Equation54177 G) : Equation54179 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) X0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54177 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54177 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l7 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54177 X0 sK2 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l8 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54177 X0 (sK1 ◇ sK1) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 X0]
  have l9 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 sK2
    conv => enter [1]; rw [h54177 X0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [l3 sK2 X0]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54177 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54177 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (X0 ◇ sK1)]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l11 sK1 sK2 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 X0]
  have l14 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [h54177 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l9 X0 sK2]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54177 X0 sK1 (sK1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l8 X0 sK1 X0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l17 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((X0 ◇ sK1) ◇ X1)) = (((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← l12 sK1 sK2 X0]
  have l18 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((X0 ◇ sK1) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l17 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X1]
  have l19 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l18 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l20 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [l12 sK1 sK2 sK1]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1) X0]
  have l22 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l7 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) sK1]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK2 ◇ sK2) ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 ((sK2 ◇ sK2) ◇ sK1)]
  have l25 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← h54177 sK1 (sK1 ◇ sK1) (sK2 ◇ sK2)]
  have l26 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l22 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK1]
    conv => enter [1]; rw [← l25 sK1 sK2]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK2)]
  have l29 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ sK2)]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l32 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← l12 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l33 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54177 sK1 X0 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l23 sK1 sK2]
  have l34 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [l12 sK1 sK2 sK1]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l26 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [l12 sK1 sK2 sK1]
  have l37 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [l36 sK1 sK2]
  have l38 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54177 (sK1 ◇ (sK2 ◇ sK2)) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l30 sK1 sK2]
  have l39 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l38 sK1 sK2 X0]
    conv => enter [1]; rw [← l19 sK1 sK2 (sK1 ◇ sK1) X0]
  have l40 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l39 sK1 sK2 X0]
    conv => enter [1]; rw [l21 sK1 sK2 (sK1 ◇ sK1)]
  have l41 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l40 sK1 sK2 X0]
    conv => enter [1]; rw [← l15 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l42 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l41 sK1 sK2 X0]
  have l43 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1)) = ((X0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h4512 X0 ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l6 X0 sK1 sK2]
  have l44 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l43 X0 sK1 sK2 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l45 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [← l44 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
  have l46 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l16 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l31 sK0 sK1 sK2]
  have l47 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l48 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l14 (sK1 ◇ (sK2 ◇ sK2)) sK2]
  have l49 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l48 sK1 sK2]
  have l50 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l49 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l51 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l47 sK1 sK2]
    conv => enter [1]; rw [← l50 sK1 sK2]
  have l52 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h54177 X0 (sK1 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h54177 (sK1 ◇ (sK2 ◇ sK2)) X0 sK0]
  have l53 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l52 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l45 X0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) sK2]
  have l54 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l46 sK1 X0 sK2]
    conv => enter [1]; rw [← l53 X0 sK1 sK2 X0]
  have l55 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l54 X0 sK1 sK2]
    conv => enter [1, 2]; rw [l34 sK1 sK2]
  have l56 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l55 X0 sK1 sK2]
  have l57 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l51 sK1 sK2]
    conv => enter [1]; rw [l56 X0 sK1 sK2]
  have l58 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [← h54177 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 2]; rw [← l57 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK2]
  have l59 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ X1) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [← l57 X0 sK1 sK2]
  have l60 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l59 X0 sK1 X1 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK2)) X1]
  have l61 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l58 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ sK2))]
  have l62 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ X1)) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l60 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X1]
  have l63 : ∀ X0 sK1 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [l61 X0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l33 sK1 (sK1 ◇ sK1) X0]
  have l64 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l62 X0 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l63 X0 sK1 X1]
  have l65 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X1 ◇ X0)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l64 X0 sK1 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) (X1 ◇ X0)]
  have l66 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l5 X0 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l65 X0 sK1 sK2 X0]
  have l67 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l66 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l37 sK1 sK2]
  have l68 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l67 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l51 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l68 x y z]

theorem Equation4512_54177_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54177 : Equation54177 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54177 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53917_implies_Equation53968 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53917 : Equation53917 G) : Equation53968 G := by
  have l0 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((X0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h53917 sK0 sK1 X0]
    conv => enter [1]; rw [h53917 sK1 (X0 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1, 2, 2]; rw [← h53917 sK0 sK1 X0]
  have l1 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l0 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK1) (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h53917 sK0 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53917 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 X0]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53917 sK2 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h53917 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation53917_implies_Equation53812 (G : Type*) [Magma G] (h53917 : Equation53917 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h53917 x x y]

@[equational_result]
theorem Equation54176_implies_Equation54174 (G : Type*) [Magma G] (h54176 : Equation54176 G) : Equation54174 G := by
  intro x y
  conv => enter [1]; rw [h54176 x y x]

@[equational_result]
theorem Equation54176_implies_Equation54175 (G : Type*) [Magma G] (h54176 : Equation54176 G) : Equation54175 G := by
  intro x y
  conv => enter [1]; rw [h54176 x y y]

theorem Equation4512_54176_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54176 : Equation54176 G) : Equation53808 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l1 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h54176 X1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54176 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l1 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54176 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h54176 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
  have l7 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l7 sK0 X0 sK1]
    conv => enter [1]; rw [← l2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation53934_implies_Equation53897 (G : Type*) [Magma G] (h53934 : Equation53934 G) : Equation53897 G := by
  intro x y
  conv => enter [1]; rw [h53934 x y y]

@[equational_result]
theorem Equation53934_implies_Equation53860 (G : Type*) [Magma G] (h53934 : Equation53934 G) : Equation53860 G := by
  intro x y
  conv => enter [1]; rw [h53934 x y x]

theorem Equation4512_53934_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53934 : Equation53934 G) : Equation53822 G := by
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
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l4 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l13 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l12 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53934 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l14 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [l9 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53934 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h53934 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l15 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53934 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l21 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0]
  have l26 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l20 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [l26 sK1 sK0 X0]
  have l28 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l20 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l28 sK0]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l29 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [← l30 sK0]
  have l33 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2]; rw [l33 sK0]
  have l35 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
  have l36 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l35 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l36 sK0 X0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l40 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l38 sK0 X0 sK1]
  have l41 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l40 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l42 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l41 sK1 sK0 X0]
  have l43 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0 X0]
    conv => enter [1]; rw [← l42 sK0 X0 sK1]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53934 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1]; rw [← l43 sK1 sK0 X0]
  have l45 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l44 sK0 X0 sK1]
  have l46 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l27 sK1 sK0 (sK0 ◇ X0)]
  have l47 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53934 sK0 X0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l46 sK1 sK0 X0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l47 sK0 X0 sK0]
    conv => enter [1]; rw [← l45 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0]
    conv => enter [1]; rw [← h53934 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l50 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l49 sK0 X0]
  have l51 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l50 sK0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l52 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l51 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l52 sK0]
    conv => enter [1]; rw [← l30 sK0]
  have l54 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l53 sK0]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l54 sK0]
    conv => enter [1]; rw [← l27 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l54 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l55 sK1 sK0]
  have l58 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [← l57 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [← l58 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l59 x y]

theorem Equation4512_54174_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54174 : Equation54174 G) : Equation54175 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54174 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h54174 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54174 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l4 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_53897_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53897 : Equation53897 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53897 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h53897 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← h53897 sK0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53897 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← h53897 sK0 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [h53897 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h53897 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [← h53897 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h53897 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53897 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← h53897 sK0 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation54140_implies_Equation54105 (G : Type*) [Magma G] (h54140 : Equation54140 G) : Equation54105 G := by
  intro x y z
  conv => enter [1]; rw [h54140 x y z y]

@[equational_result]
theorem Equation54140_implies_Equation54122 (G : Type*) [Magma G] (h54140 : Equation54140 G) : Equation54122 G := by
  intro x y z
  conv => enter [1]; rw [h54140 x y z z]

@[equational_result]
theorem Equation54140_implies_Equation53842 (G : Type*) [Magma G] (h54140 : Equation54140 G) : Equation53842 G := by
  intro x y z
  conv => enter [1]; rw [h54140 x x y z]

@[equational_result]
theorem Equation54029_implies_Equation54025 (G : Type*) [Magma G] (h54029 : Equation54029 G) : Equation54025 G := by
  intro x y z
  conv => enter [1]; rw [h54029 x y y z]

@[equational_result]
theorem Equation54029_implies_Equation54028 (G : Type*) [Magma G] (h54029 : Equation54029 G) : Equation54028 G := by
  intro x y z
  conv => enter [1]; rw [h54029 x y z z]

theorem Equation4512_54029_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54029 : Equation54029 G) : Equation53811 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54029 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_54105_implies_Equation54088 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54105 : Equation54105 G) : Equation54088 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h54105 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54105 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation54105_implies_Equation54060 (G : Type*) [Magma G] (h54105 : Equation54105 G) : Equation54060 G := by
  intro x y
  conv => enter [1]; rw [h54105 x y y]

@[equational_result]
theorem Equation54105_implies_Equation53822 (G : Type*) [Magma G] (h54105 : Equation54105 G) : Equation53822 G := by
  intro x y
  conv => enter [1]; rw [h54105 x x y]

theorem Equation4512_54025_implies_Equation54022 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54025 : Equation54025 G) : Equation54022 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h54025 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X3]
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54025 X0 X1 (X0 ◇ X2)]
    conv => enter [1]; rw [l4 X0 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation54025_implies_Equation54024 (G : Type*) [Magma G] (h54025 : Equation54025 G) : Equation54024 G := by
  intro x y
  conv => enter [1]; rw [h54025 x y y]

theorem Equation4512_54025_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54025 : Equation54025 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54025 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation54088_implies_Equation54050 (G : Type*) [Magma G] (h54088 : Equation54088 G) : Equation54050 G := by
  intro x y
  conv => enter [1]; rw [h54088 x y y]

@[equational_result]
theorem Equation54088_implies_Equation54013 (G : Type*) [Magma G] (h54088 : Equation54088 G) : Equation54013 G := by
  intro x y
  conv => enter [1]; rw [h54088 x y x]

theorem Equation4512_54088_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54088 : Equation54088 G) : Equation53822 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54088 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_54022_implies_Equation54021 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54022 : Equation54022 G) : Equation54021 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54022 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54022_implies_Equation54020 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54022 : Equation54022 G) : Equation54020 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54022 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_54022_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54022 : Equation54022 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54022 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54113_implies_Equation54140 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54113 : Equation54113 G) : Equation54140 G := by
  have l0 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ X0)) = ((sK2 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [h54113 X0 sK1 sK2 X1]
    conv => enter [1]; rw [h4512 sK2 sK1 (X1 ◇ X0)]
  have l1 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← h54113 (sK2 ◇ sK1) (sK2 ◇ sK1) sK0 sK0]
  have l2 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h54113 (sK2 ◇ sK1) (sK2 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
  have l3 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h54113 (sK2 ◇ sK1) X0 sK1 sK0]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h54113 (sK2 ◇ sK1) sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
  have l5 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [h54113 (sK2 ◇ sK1) (sK2 ◇ sK1) sK2 X0]
    conv => enter [1]; rw [← l3 sK2 sK1 X0 sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [l2 sK2 sK1 sK0]
  have l7 : ∀ sK2 sK1 X0 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0 sK3 sK0
    conv => enter [1]; rw [l0 (sK2 ◇ sK1) sK1 sK2 sK3]
    conv => enter [1]; rw [h54113 (sK2 ◇ sK1) sK3 X0 sK0]
  have l8 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54113 (sK2 ◇ sK1) X0 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l5 sK2 sK1 X0 sK2]
  have l9 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l8 sK2 sK1 X0]
    conv => enter [1]; rw [l2 sK2 sK1 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK2 sK1 sK0]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK2 sK1 sK0]
  have l12 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l14 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l6 sK0 sK2 sK1]
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
  have l15 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l14 sK1 sK2 sK0]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l7 sK2 sK1 (sK2 ◇ sK1) sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l17 : ∀ sK0 sK2 sK1 X0 sK3 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0 sK3
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l7 sK2 sK1 X0 sK3 sK0]
  have l18 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h54113 (sK0 ◇ (sK2 ◇ sK1)) X0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 sK2 sK1 X0 sK0]
  have l19 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l7 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 sK2 sK2]
  have l20 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l15 sK0 sK2 sK1]
  have l21 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l19 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l22 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54113 (sK2 ◇ sK1) X0 (sK2 ◇ (sK2 ◇ sK1)) sK2]
    conv => enter [1]; rw [l20 sK2 sK2 sK1 X0]
  have l23 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l22 sK2 sK1 X0]
    conv => enter [1]; rw [← l21 sK2 sK1]
  have l24 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [← h54113 (sK2 ◇ sK1) X0 X1 sK0]
    conv => enter [1]; rw [l9 sK2 sK1 X0 sK0]
  have l25 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [l24 X1 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
  have l26 : ∀ X1 X0 sK0 sK2 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X1 X0 sK0 sK2 sK1
    conv => enter [1]; rw [l25 X1 X0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l21 sK2 sK1]
  have l27 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54113 sK1 sK2 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK2 ◇ sK1))]
  have l28 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54113 sK1 sK2 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l23 sK2 sK1 sK2]
  have l29 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h54113 sK1 sK2 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l9 sK2 sK1 sK2 sK0]
  have l30 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l27 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [← h54113 (sK2 ◇ sK1) X1 sK1 sK2]
  have l31 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l29 sK1 sK2 X0]
    conv => enter [1]; rw [l26 X0 (sK1 ◇ (sK2 ◇ sK1)) X0 sK2 sK1]
  have l32 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [← l31 X0 sK1 sK2]
  have l33 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l30 sK1 sK2 sK0]
  have l34 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l33 sK0 sK2 sK1]
  have l35 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l34 sK1 sK2 sK0]
  have l36 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK3]
    conv => enter [1]; rw [← l35 sK3 sK0 sK2 sK1]
  have l37 : ∀ X1 sK0 sK2 sK1 X0 : G, (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h54113 sK1 sK0 X1 sK2]
    conv => enter [1]; rw [h54113 sK1 sK0 X0 sK2]
  have l38 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l37 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK0 sK2 sK1 X0]
  have l39 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l38 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l39 x y z w]

theorem Equation4512_54113_implies_Equation54075 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54113 : Equation54113 G) : Equation54075 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l3 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h54113 (sK1 ◇ sK0) sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l6 sK1 sK0]
    conv => enter [1]; rw [← h54113 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l8 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (X1 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h54113 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [← l3 sK2 sK0 sK1]
  have l9 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← h54113 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← h54113 X0 sK0 X1 (sK1 ◇ sK0)]
  have l11 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54113 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ X0))]
  have l12 : ∀ sK2 sK0 X1 X2 X0 : G, ((sK2 ◇ sK0) ◇ (X1 ◇ (X2 ◇ X0))) = (sK2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK2 sK0 X1 X2 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (X1 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h54113 X0 X1 sK0 X2]
  have l13 : ∀ sK2 sK0 sK1 X1 X2 X0 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X2 ◇ X0)))) = ((sK2 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK2 sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [← l2 sK2 sK0 sK1 (X1 ◇ (X2 ◇ X0))]
    conv => enter [1, 2]; rw [← h54113 X0 X1 (sK1 ◇ sK0) X2]
  have l14 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0))) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [h54113 X0 (sK1 ◇ sK0) (sK2 ◇ sK0) X1]
    conv => enter [1]; rw [l2 sK2 sK0 sK1 (X1 ◇ X0)]
  have l15 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l9 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l16 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h54113 (sK1 ◇ sK0) X0 sK1 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1 X0 sK1]
  have l17 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← h54113 (sK1 ◇ sK0) X0 X1 sK0]
    conv => enter [1]; rw [← h54113 sK0 X0 (sK1 ◇ sK0) sK1]
  have l18 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l15 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← l11 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l16 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l20 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← l17 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0 sK1]
    conv => enter [1]; rw [← l18 X1 X0 sK1 sK0]
  have l21 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l19 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [l13 sK2 sK0 sK1 X0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 (sK1 ◇ sK0) (sK1 ◇ sK0) sK1 X0 sK1]
    conv => enter [1]; rw [← l20 sK0 X0 sK1 sK1]
  have l23 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l21 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [l12 sK2 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l24 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l22 sK1 sK0 X0]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l23 sK1 sK0 X0 sK1]
    conv => enter [1]; rw [← l14 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l26 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l24 sK1 sK0 X0]
    conv => enter [1]; rw [← h54113 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l17 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 sK0 sK0]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [← h54113 sK0 X0 (sK1 ◇ sK0) sK1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l29 sK0 sK1 X0]
  have l31 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54113 sK0 sK2 X0 sK2]
    conv => enter [1]; rw [l28 sK0 sK2]
  have l32 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK0]
    conv => enter [1]; rw [← l31 X0 sK2 sK0]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l30 sK0 sK1 sK1]
    conv => enter [1]; rw [l32 sK0 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l33 x y y z]

theorem Equation4512_54113_implies_Equation54067 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54113 : Equation54113 G) : Equation54067 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54113 (sK0 ◇ sK0) (sK0 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 X0 X1 sK1 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h54113 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← h54113 X0 sK0 X1 (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54113 (sK0 ◇ sK0) (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [h54113 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l10 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54113 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ X0))]
  have l11 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h54113 X0 sK0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X1 ◇ X0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54113 sK0 (sK1 ◇ sK0) sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54113 sK0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 sK1 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 (sK1 ◇ sK0) sK0 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 X0 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h54113 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 (sK0 ◇ sK0) X0 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK0 sK1 sK0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← h54113 sK0 X0 (sK0 ◇ sK0) sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l23 sK0 sK1 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 X0]
  have l29 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l28 sK0 sK2]
    conv => enter [1]; rw [h54113 sK0 sK2 X0 sK0]
  have l30 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l29 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l30 x y y z]

theorem Equation4512_54113_implies_Equation54063 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54113 : Equation54113 G) : Equation54063 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (((sK1 ◇ sK2) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [h4512 sK1 sK2 (sK0 ◇ sK2)]
  have l3 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK0 ◇ sK2) X0]
  have l4 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK2 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l4 sK2 sK0]
  have l6 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [l5 sK0 sK2]
  have l7 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l6 sK2 sK0]
    conv => enter [1]; rw [← h54113 (sK0 ◇ sK2) sK0 sK2 (sK2 ◇ (sK0 ◇ sK2))]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) = (sK1 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [l7 sK2 sK0]
  have l9 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54113 (sK0 ◇ sK2) (sK0 ◇ sK2) sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l9 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54113 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) (sK0 ◇ sK2) sK0]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l1 sK0 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l10 sK0 sK2]
  have l12 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))))) = (sK1 ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK1 sK2 sK0 ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l11 sK0 sK2]
  have l13 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h54113 (sK0 ◇ sK2) sK0 sK1 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54113 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) (sK0 ◇ sK2) (sK0 ◇ sK2)]
  have l15 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [← l14 sK0 sK2]
  have l16 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ (sK0 ◇ sK2))]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l16 sK0 sK2]
    conv => enter [1]; rw [← h54113 (sK0 ◇ sK2) (sK2 ◇ (sK0 ◇ sK2)) sK0 sK0]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54113 (sK0 ◇ sK2) sK0 (sK0 ◇ sK2) (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l17 sK0 sK2]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [l18 sK0 sK2]
  have l20 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54113 (sK0 ◇ sK2) sK0 sK2 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l20 sK2 sK0]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [l21 sK0 sK2]
  have l23 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1, 2]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [h54113 ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2)) X0 X1]
  have l24 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54113 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ X0))]
  have l25 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ (sK0 ◇ sK2))) = (((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l24 (sK0 ◇ sK2) X1 sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l23 sK2 sK0 sK0 X1]
  have l26 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l25 sK0 sK2 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)))]
  have l27 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l24 (sK0 ◇ sK2) sK0 (sK2 ◇ (sK0 ◇ sK2)) (sK0 ◇ sK2) (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [← l26 sK0 sK2 X1]
  have l28 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l27 sK0 sK2 X1]
    conv => enter [1]; rw [← h54113 sK2 X1 (sK0 ◇ sK2) sK0]
  have l29 : ∀ sK0 sK2 X1 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = (sK2 ◇ (X1 ◇ sK2)) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l15 sK0 sK2]
    conv => enter [1]; rw [l28 sK0 sK2 X1]
  have l30 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h54113 sK2 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK2))]
  have l31 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l30 sK2 sK0 sK2 X1]
    conv => enter [1]; rw [← h54113 (sK0 ◇ sK2) X1 sK2 sK0]
  have l32 : ∀ sK2 sK0 X1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (X1 ◇ sK2)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l31 sK2 sK0 X1]
    conv => enter [1]; rw [← h54113 sK2 X1 (sK0 ◇ sK2) sK0]
  have l33 : ∀ sK2 sK0 X1 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [l32 sK2 sK0 X0]
    conv => enter [1]; rw [h54113 sK2 X0 X1 sK0]
  have l34 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l29 sK0 sK2 sK0]
    conv => enter [1]; rw [h54113 sK2 sK0 X0 sK1]
  have l35 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l33 sK2 sK0 sK0 (sK2 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [l34 sK0 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l35 x y y z]

theorem Equation4512_54113_implies_Equation53854 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54113 : Equation54113 G) : Equation53854 G := by
  have l0 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h54113 sK1 sK1 X0 sK0]
  have l1 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 X0 sK0]
  have l2 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l1 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK1))]
  have l3 : ∀ sK1 sK0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l2 sK1 sK1 X1 sK0]
    conv => enter [1]; rw [← h54113 (sK0 ◇ sK1) X1 sK1 sK1]
  have l4 : ∀ sK1 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l3 sK1 sK1 X1]
    conv => enter [1]; rw [← h54113 sK1 X1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 X1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X1 X0 sK0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [h54113 sK1 X0 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_54113_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54113 : Equation54113 G) : Equation53850 G := by
  have l0 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 sK0]
  have l2 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [← h54113 (sK2 ◇ (sK0 ◇ sK0)) sK2 X0 X1]
    conv => enter [1, 2]; rw [← l1 sK2 sK0]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ X0)))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h54113 X0 X1 (X2 ◇ X3) X4]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ (X4 ◇ X0))]
  have l4 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [h54113 X0 sK0 (sK2 ◇ sK0) X1]
    conv => enter [1]; rw [l0 sK2 sK0 (X1 ◇ X0)]
  have l5 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (sK2 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [l2 X0 sK2 X1 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK0)]
  have l6 : ∀ sK0 X0 sK2 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK2 X1
    conv => enter [1]; rw [l4 sK0 sK0 sK2 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l5 X0 sK2 X1 sK0]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0 sK0 X1]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) X1 sK0 sK0 sK0]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l7 sK0 X1]
    conv => enter [1]; rw [← h54113 sK0 X1 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X1]
  have l10 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X1]
  have l11 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK2]
    conv => enter [1]; rw [h54113 sK0 sK2 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_54037_implies_Equation54029 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation54029 G := by
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
  have l3 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h54037 sK2 X0 sK1 X1]
  have l4 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l3 sK2 sK1 X0 X1]
  have l5 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l7 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK3 ◇ sK0) ◇ X0) X1]
  have l8 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ ((sK3 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l7 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ sK0) X0 X1]
  have l9 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l8 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h54037 sK2 X0 (sK3 ◇ sK0) X1]
  have l10 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l9 sK2 sK3 sK0 X0 X1]
  have l11 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← l6 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l13 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l12 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h54037 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK2 X0]
  have l15 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK2 sK1 X0]
  have l16 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l4 sK2 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [← l15 sK2 sK1 X0]
  have l17 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l16 sK2 sK1 sK2]
    conv => enter [1]; rw [← h54037 sK2 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) sK2]
  have l18 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← l4 sK2 sK1 sK1 (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK3 sK0]
  have l19 : ∀ sK2 sK3 sK1 sK0 X0 : G, (sK2 ◇ (sK3 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK2 sK3 sK1 sK0 X0
    conv => enter [1]; rw [← l4 sK2 sK1 sK3 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK3 sK0 X0]
  have l20 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK2 sK1 X0]
    conv => enter [1]; rw [l4 sK2 sK1 (sK2 ◇ sK1) X0]
  have l21 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK2 sK1 X0 X1]
  have l22 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l21 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK1 X0 sK2 sK2]
  have l23 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l20 sK2 sK1 X0]
    conv => enter [1]; rw [← l17 sK2 sK1]
  have l24 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK3 ◇ sK2)) = (sK2 ◇ ((sK3 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK2 sK3 sK2 sK0 sK2]
    conv => enter [1]; rw [l4 sK2 sK2 (sK3 ◇ sK0) sK2]
  have l25 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l4 sK2 sK1 sK2 (sK3 ◇ sK0)]
  have l26 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l18 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [l4 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK2))]
  have l27 : ∀ sK2 sK1 sK3 sK0 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l28 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 sK2]
    conv => enter [1]; rw [← l4 sK2 sK1 sK1 (sK2 ◇ sK1)]
  have l29 : ∀ sK2 sK3 sK0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = (sK2 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [← l24 sK2 sK3 sK0]
  have l30 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l23 sK2 sK1 sK2]
    conv => enter [1]; rw [← l26 sK2 sK1]
  have l31 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) = ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l29 sK2 sK3 sK0]
    conv => enter [1]; rw [← l4 sK2 sK1 sK3 sK0]
  have l32 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l30 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK2]
  have l33 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ sK1) ◇ sK2) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l25 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l32 sK2 sK1]
  have l34 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l27 sK2 sK1 sK3 sK0]
  have l35 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [← l34 sK1 sK2 sK3 sK0]
  have l36 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l28 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l37 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l36 sK1 sK2]
  have l38 : ∀ sK2 sK3 sK0 X0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK2 ◇ sK1) ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK2 sK3 sK0 X0 sK1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l31 sK2 sK3 sK0 sK1]
  have l39 : ∀ sK2 sK1 sK3 sK0 X0 : G, ((sK2 ◇ sK1) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [← l38 sK2 sK3 sK0 X0 sK1]
  have l40 : ∀ sK2 sK1 sK3 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK2 sK1 sK3 sK0 X0
    conv => enter [1]; rw [← l10 sK2 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [← l39 sK2 sK1 sK3 sK0 X0]
  have l41 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK3 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l40 sK2 sK2 sK3 sK0 sK2]
    conv => enter [1]; rw [l4 sK2 sK2 (sK3 ◇ sK0) sK2]
  have l42 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l41 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK0) sK2]
  have l43 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l42 sK2 sK3 sK0]
    conv => enter [1]; rw [l31 sK2 sK3 sK0 sK1]
  have l44 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l25 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l43 sK2 sK1 sK3 sK0]
  have l45 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l33 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK2]
  have l46 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l35 sK1 sK2 sK3 sK0]
  have l47 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l46 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
  have l48 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l22 sK1 sK2 sK2 X0]
    conv => enter [1]; rw [← l47 sK1 sK2 sK3 sK0 X0]
  have l49 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l22 sK1 sK2 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1]
  have l50 : ∀ sK1 sK2 X0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l51 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l22 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l50 sK1 sK2 X0]
  have l52 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l51 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
  have l53 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l22 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [← l52 sK1 sK2 sK1]
  have l54 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l44 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK3 ◇ sK0)]
  have l55 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l45 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l54 sK1 sK2 sK3 sK0]
  have l56 : ∀ sK1 sK2 X0 sK3 sK0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l55 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK3 ◇ sK0) X0]
  have l57 : ∀ sK1 sK2 X0 sK3 sK0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK2) ◇ X0) = (sK1 ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l56 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l22 sK1 sK2 (sK3 ◇ sK0) X0]
  have l58 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ X0)) = (sK1 ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) sK2 X0]
    conv => enter [1]; rw [l57 sK1 sK2 X0 sK3 sK0]
  have l59 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l22 sK1 sK2 sK2 sK1]
    conv => enter [1]; rw [l58 sK1 sK2 sK1 sK3 sK0]
  have l60 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l59 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 ((sK3 ◇ sK0) ◇ sK1)]
  have l61 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK3 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l60 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l4 sK2 sK1 (sK3 ◇ sK0) sK1]
  have l62 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l61 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK0) sK2]
  have l63 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK3 ◇ sK0)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l62 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [l31 sK2 sK3 sK0 sK1]
  have l64 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l63 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l44 sK2 sK1 sK3 sK0]
  have l65 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l64 sK2 sK1 sK3 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 sK3 sK0]
  have l66 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l5 sK1 sK2]
    conv => enter [1]; rw [l65 sK1 sK2 sK3 sK0]
  have l67 : ∀ X1 sK2 sK3 sK0 sK1 X0 : G, (X1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X1)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X1 sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [h54037 X1 (sK2 ◇ (sK3 ◇ sK0)) sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l68 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l59 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h54037 X0 (sK3 ◇ sK0) sK1 sK1]
  have l69 : ∀ X1 sK3 sK0 sK2 X0 : G, (X1 ◇ ((sK3 ◇ sK0) ◇ X1)) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro X1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [h54037 X1 (sK3 ◇ sK0) sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK3 ◇ sK0) X0]
  have l70 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X1 ◇ ((sK3 ◇ sK0) ◇ X1)) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l67 X1 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [← l69 X1 sK3 sK0 sK2 X1]
  have l71 : ∀ X1 sK1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro X1 sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l68 X1 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l70 X1 sK1 sK2 sK3 sK0 X0]
  have l72 : ∀ sK1 sK2 X0 sK3 sK0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l66 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l73 : ∀ sK1 sK2 X0 sK3 sK0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l72 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0 X0]
  have l74 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l49 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l73 sK1 sK2 X0 sK1 sK1]
  have l75 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l74 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l76 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l75 sK1 sK2 sK1]
    conv => enter [1]; rw [l22 sK1 sK2 (sK2 ◇ sK1) sK1]
  have l77 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l76 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l78 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l53 sK1 sK2]
    conv => enter [1, 2]; rw [← l77 sK1 sK2]
  have l79 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54037 X0 X1 (sK1 ◇ (sK2 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← l71 X0 sK1 sK2 X0 X0 (X1 ◇ X0)]
  have l80 : ∀ X0 X1 sK3 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 X1 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h54037 X0 sK3 X1 sK0]
    conv => enter [1]; rw [l79 X0 sK3 sK1 sK2]
  have l81 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l78 sK1 sK2]
    conv => enter [1]; rw [← l80 sK1 sK2 sK3 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l81 x y z w]

theorem Equation4512_54037_implies_Equation54039 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation54039 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ X1) = (sK1 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ X0) X1]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ X1) = (sK1 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l3 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ sK0) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK0 X0 X1]
    conv => enter [1]; rw [← h54037 sK1 X0 sK0 X1]
  have l4 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l3 sK1 sK0 X0 X1]
  have l5 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK0 X0 X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK0 X0 X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h54037 sK0 X0 sK1 sK1]
  have l8 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l4 sK1 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK1 sK0 X0 X1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l4 sK1 sK0 sK1 sK0]
  have l10 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0 (sK2 ◇ (sK2 ◇ sK1))]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0 (sK1 ◇ sK0)]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54037 sK1 X0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l8 sK1 sK1 X0 sK1]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 X0]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l10 sK1 sK0 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l15 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l18 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l20 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l7 sK0 sK1 sK1 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 X0]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK0]
  have l22 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l22 sK0 sK1 X0]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 sK0]
  have l26 : ∀ X1 sK2 sK1 sK0 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro X1 sK2 sK1 sK0 X0
    conv => enter [1]; rw [h54037 X1 (sK2 ◇ (sK2 ◇ sK1)) sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l27 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ X1)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1]; rw [h54037 X1 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l28 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ ((sK2 ◇ sK1) ◇ X1)) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h54037 X1 (sK2 ◇ sK1) sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 (sK2 ◇ sK1) X0]
  have l29 : ∀ X1 sK0 sK2 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = (X1 ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro X1 sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l26 X1 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← l28 X1 sK2 sK1 X1]
  have l30 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ (sK1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l27 X1 sK1 sK2 X1]
    conv => enter [1]; rw [← l29 X1 sK0 sK2 sK1 X0]
  have l31 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h54037 X0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK0 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 sK2]
  have l32 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK0 X0 X0]
    conv => enter [1]; rw [l31 X0 sK0 X0 sK1]
  have l33 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54037 X0 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  have l34 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l32 X0 sK1 sK0]
    conv => enter [1]; rw [l33 X0 sK1 sK0]
  have l35 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54037 X0 X1 sK1 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 sK0 X1]
  have l36 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l35 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← l34 X0 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l38 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [← h54037 X0 sK2 sK2 sK1]
    conv => enter [1]; rw [l36 X0 sK2 sK0 sK1]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l39 x y z]

theorem Equation4512_54037_implies_Equation54035 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation54035 G := by
  have l0 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l0 sK2 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l1 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK2 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l2 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0]
    conv => enter [1]; rw [← h54037 sK2 (sK1 ◇ sK1) sK1 X0]
  have l5 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) sK2]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK2)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK2 sK1 X0]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK2) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) sK2]
  have l8 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK2) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [← l5 sK2 sK1 sK0]
  have l9 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK2) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l8 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 sK1 X2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK1 ◇ X2))) = ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1 sK1 X2
    conv => enter [1]; rw [← h54037 (sK0 ◇ X0) sK1 X1 X2]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l11 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54037 sK0 X0 (sK1 ◇ sK0) X1]
  have l12 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h54037 sK0 X0 (sK2 ◇ (sK1 ◇ sK1)) X1]
  have l13 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK2) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l7 sK0 sK2 sK1 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54037 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) X0 sK1 sK0]
  have l14 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK2 sK1]
    conv => enter [1]; rw [l13 sK0 sK2 sK1 X0]
  have l15 : ∀ sK0 X0 X1 sK1 X2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK1 ◇ X2))) = (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 sK1 X2
    conv => enter [1]; rw [l10 sK0 X0 X1 sK1 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l16 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l12 sK0 sK2 sK1 X0 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))]
  have l17 : ∀ sK0 X0 X1 sK1 X2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK1 ◇ X2))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1 sK1 X2
    conv => enter [1]; rw [l15 sK0 X0 X1 sK1 X2]
    conv => enter [1]; rw [← h54037 sK0 (sK1 ◇ sK0) X0 X0]
  have l18 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ X0) ◇ (X1 ◇ (sK1 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l17 sK0 X0 X1 sK1 X2]
  have l19 : ∀ sK0 sK1 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK1 ◇ X2))]
  have l20 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l19 sK0 sK1 sK0 X1 sK0]
    conv => enter [1]; rw [← h54037 sK0 X1 sK0 (sK1 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 sK0 sK1 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l20 sK0 sK1 sK1]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [← l20 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [l11 sK0 sK1 sK0 X0]
  have l24 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← l16 sK0 sK2 sK1 sK0]
  have l25 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l24 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1 X1 sK0]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l20 sK0 sK1 sK1]
    conv => enter [1]; rw [l25 sK0 sK1 sK0 X0]
  have l27 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54037 X0 X1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l26 sK0 sK1 (X1 ◇ X0)]
  have l28 : ∀ X0 sK2 sK1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK1 sK0
    conv => enter [1]; rw [← h54037 X0 sK1 sK2 sK1]
    conv => enter [1]; rw [l27 X0 sK1 sK0 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

theorem Equation4512_54037_implies_Equation54017 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation54017 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ X0) X1]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK1 X0 sK2 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 (sK1 ◇ sK2)]
  have l5 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← l4 sK0 sK2 sK1]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ sK0)) (sK1 ◇ sK2) X0]
  have l7 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l8 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h54037 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l9 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) sK0]
  have l10 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 X0 X1]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [← l3 sK1 sK2 sK2 X0]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK0 X0 sK1 sK1]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [← l11 sK1 sK2 X0]
  have l14 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ X0) ◇ X1)) = (((sK1 ◇ sK2) ◇ sK1) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l11 sK1 sK2 X0]
  have l15 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l14 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) sK1 X1]
  have l16 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK1]
  have l17 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l15 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l12 sK0 sK1 sK2 sK2 sK0]
    conv => enter [1]; rw [l16 sK0 sK1 sK2 sK0]
  have l19 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← l3 sK1 sK2 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l17 sK1 sK2 X1 sK1]
  have l20 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ sK2) ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 sK1]
    conv => enter [1]; rw [l19 sK1 sK2 X1]
  have l21 : ∀ sK1 sK2 sK0 X1 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
    conv => enter [1]; rw [l20 sK1 sK2 X1]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [l11 sK1 sK2 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK0)]
  have l24 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l25 : ∀ sK0 X0 X1 sK2 X2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK2 ◇ X2))) = ((sK0 ◇ X0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1 sK2 X2
    conv => enter [1]; rw [← h54037 (sK0 ◇ X0) sK2 X1 X2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 X0]
  have l26 : ∀ sK0 X0 X1 sK2 X2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK2 ◇ X2))) = (sK0 ◇ (X0 ◇ ((sK2 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 sK2 X2
    conv => enter [1]; rw [l25 sK0 X0 X1 sK2 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK2 ◇ sK0) ◇ X0)]
  have l27 : ∀ sK0 X0 X1 sK2 X2 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK2 ◇ X2))) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 X1 sK2 X2
    conv => enter [1]; rw [l26 sK0 X0 X1 sK2 X2]
    conv => enter [1]; rw [← h54037 sK0 (sK2 ◇ sK0) X0 X0]
  have l28 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = ((sK0 ◇ X0) ◇ (X1 ◇ (sK2 ◇ X2))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [← l27 sK0 X0 X1 sK2 X2]
  have l29 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ X2)))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [l28 sK0 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK2 ◇ X2))]
  have l30 : ∀ sK0 sK2 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X1 ◇ sK0)) := by
    intro sK0 sK2 X1
    conv => enter [1]; rw [l29 sK0 sK2 sK0 X1 sK0]
    conv => enter [1]; rw [← h54037 sK0 X1 sK0 (sK2 ◇ sK0)]
  have l31 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l24 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ sK0) X0]
  have l32 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK2 X0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 sK2 (sK2 ◇ sK0) X0]
  have l33 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l32 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l34 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X1) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l33 sK0 sK2 X0]
    conv => enter [1]; rw [← l33 sK0 sK2 X1]
  have l35 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l34 sK0 sK2 X0 ((sK1 ◇ sK2) ◇ sK0)]
    conv => enter [1]; rw [l9 sK0 sK2 sK1 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← l30 sK0 sK2 (sK1 ◇ sK2)]
  have l37 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK2 sK0 sK1]
  have l38 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l30 sK0 sK2 sK2]
    conv => enter [1]; rw [l35 sK0 sK2 sK0 sK1]
  have l39 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l38 sK0 sK2 sK0]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l35 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK2]
  have l41 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l38 sK0 sK2 sK0]
    conv => enter [1]; rw [l40 sK0 sK0 sK2]
  have l42 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l38 sK0 sK2 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [l21 sK1 sK2 sK0 sK2]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l45 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
    conv => enter [1]; rw [l44 sK0 sK1 sK2]
  have l46 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l45 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l47 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l46 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 (sK1 ◇ sK2) X0]
  have l48 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l47 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK0]
  have l49 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l42 sK0 sK2 sK0]
    conv => enter [1]; rw [← l48 sK0 sK2 X0 sK0]
  have l50 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1, 2]; rw [l49 sK0 sK2 X0]
    conv => enter [1]; rw [h54037 X0 (sK0 ◇ (sK2 ◇ sK0)) X1 X2]
  have l51 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1, 2]; rw [l49 sK0 sK2 (X1 ◇ X0)]
    conv => enter [1]; rw [← h54037 X0 X1 (sK0 ◇ (sK2 ◇ sK0)) X0]
  have l52 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK0))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [l50 X0 sK0 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [l35 sK0 sK2 X0 sK1]
  have l53 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK0))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [l52 X0 sK0 sK2 X1 sK1]
    conv => enter [1, 2, 2]; rw [← l37 sK0 sK1 sK2]
  have l54 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [l53 X0 sK0 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← l42 sK0 sK2 X0]
  have l55 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ sK0) ◇ sK2) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 sK2]
    conv => enter [1]; rw [h54037 sK2 sK0 X0 (sK1 ◇ sK2)]
  have l56 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h54037 sK2 sK0 sK0 (sK1 ◇ sK2)]
  have l57 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK0) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l56 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 sK2]
  have l58 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l51 X0 sK0 sK2 sK0]
    conv => enter [1]; rw [h54037 X0 sK0 sK0 (sK1 ◇ sK2)]
  have l59 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ sK0) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l57 sK2 sK0 sK1]
  have l60 : ∀ X0 X1 sK0 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK2 sK1
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l58 (X0 ◇ X1) sK0 sK2 sK1]
  have l61 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [l58 sK0 sK0 sK2 sK1]
  have l62 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l60 X0 X1 sK0 sK2 sK1]
  have l63 : ∀ X0 sK0 sK2 X1 sK1 : G, (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK0 sK2 X1 sK1
    conv => enter [1]; rw [l54 X0 sK0 sK2 X1]
    conv => enter [1]; rw [← l62 X0 X1 sK0 sK1 sK2]
  have l64 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [← l63 X0 sK0 sK2 X1 sK1]
    conv => enter [1]; rw [l58 X0 sK0 sK2 sK1]
  have l65 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h54037 X0 X1 sK2 (sK0 ◇ (X0 ◇ sK2))]
    conv => enter [1, 2]; rw [← l55 sK2 sK0 X1 X0]
  have l66 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l65 X0 X1 sK2 sK0]
    conv => enter [1, 2]; rw [← l59 sK2 sK0 sK1]
  have l67 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l66 X0 X1 sK2 sK0 sK1]
    conv => enter [1]; rw [l64 X0 sK2 sK0 sK1 sK2]
  have l68 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [← h54037 X0 sK1 X1 sK2]
    conv => enter [1]; rw [l67 X0 sK1 sK0 sK1 sK2]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l61 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l69 x z y]

theorem Equation4512_54037_implies_Equation53821 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation53821 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK3 ◇ sK0) ◇ X0) X1]
  have l2 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ ((sK3 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ sK0) X0 X1]
  have l3 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h54037 sK2 X0 (sK3 ◇ sK0) X1]
  have l4 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK2 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l3 sK2 sK3 sK0 X0 X1]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK0 X0 X1]
  have l6 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l4 sK2 sK3 sK0 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK0) sK2]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h54037 sK1 X0 sK2 sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) ((sK3 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l6 sK2 sK3 sK0 X0]
  have l9 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK2) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) sK2]
  have l10 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK2) = (sK1 ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l9 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 (sK3 ◇ sK0) sK1]
  have l11 : ∀ sK1 sK3 sK0 X0 sK2 : G, (sK1 ◇ (((sK3 ◇ sK0) ◇ sK1) ◇ X0)) = (((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK2) ◇ X0) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK1 ((sK3 ◇ sK0) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l10 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK1 sK3 sK0 X0 sK2 : G, (sK1 ◇ (((sK3 ◇ sK0) ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l11 sK1 sK3 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK2 X0]
  have l13 : ∀ sK1 sK3 sK0 X0 sK2 : G, (sK1 ◇ (((sK3 ◇ sK0) ◇ sK1) ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [l12 sK1 sK3 sK0 X0 sK2]
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0 sK2 X0]
  have l14 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK3 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l13 sK1 sK3 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ sK0) sK1 X0]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54037 sK1 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l14 sK1 sK2 sK1 sK1 sK1]
  have l16 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l15 sK1 sK2]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l16 sK1 sK2]
  have l18 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
  have l19 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ X0))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l18 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h54037 sK1 sK1 sK1 X0]
    conv => enter [1]; rw [← l19 sK1 X0 sK1]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [← l20 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l21 sK1 X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1]
  have l24 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54037 X0 X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l22 sK1 (X1 ◇ X0)]
  have l25 : ∀ X0 sK1 X1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 X1 sK3 sK0
    conv => enter [1]; rw [← l24 X0 sK3 sK1]
    conv => enter [1]; rw [h54037 X0 sK3 X1 sK0]
  have l26 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [l25 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l26 x y z w]

theorem Equation4512_54037_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54037 : Equation54037 G) : Equation53817 G := by
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
  have l5 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (((sK1 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK2) ◇ X0) X1]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) X0 X1]
  have l7 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK1 X0 (sK1 ◇ sK2) X1]
  have l8 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l7 sK1 sK2 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h54037 (sK0 ◇ sK0) X0 sK0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l13 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l14 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK1 sK2 sK1 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l15 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l17 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l8 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l4 sK0]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [l8 sK1 sK2 X0 sK1]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l8 sK1 sK2 X0 X1]
  have l20 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h54037 sK0 X0 sK1 sK1]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l18 sK1 sK2 X0]
    conv => enter [1]; rw [← h54037 (sK1 ◇ (sK1 ◇ sK2)) X0 sK1 sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 sK1 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l17 sK1 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l8 sK1 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l16 sK1 sK1 sK0]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK1]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l13 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK1]
  have l26 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← l8 sK1 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l21 sK1 sK2 X0]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l23 sK1 sK0]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l24 sK1 sK2]
  have l30 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
  have l31 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [← l28 sK1 sK2 sK0]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [l26 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK2]
  have l33 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l29 sK1 sK2]
  have l34 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l34 sK1 sK2 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l36 sK0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2 X0]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
  have l44 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l43 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0 X0]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l20 sK0 sK0 sK0 sK0 X0]
    conv => enter [1]; rw [← l44 sK0 X0 sK0 sK0]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l45 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l47 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l47 sK0 X0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l48 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l50 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l48 sK0 X0]
  have l51 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l50 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l52 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l49 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l53 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l48 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l51 sK0 X1 sK0]
  have l54 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l48 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l52 sK0]
  have l55 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54037 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l53 sK0 (X1 ◇ X0)]
  have l56 : ∀ X0 sK0 X1 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 X1 sK1 sK2
    conv => enter [1]; rw [← l55 X0 sK1 sK0]
    conv => enter [1]; rw [h54037 X0 sK1 X1 sK2]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l54 sK0]
    conv => enter [1]; rw [l56 sK0 sK0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l57 x y z]

theorem Equation4512_54075_implies_Equation54105 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54075 : Equation54075 G) : Equation54105 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h54075 (sK0 ◇ X0) X1 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l2 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54075 (X1 ◇ X0) X2 X1]
    conv => enter [1, 2]; rw [← h54075 X0 X1 X1]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54075 X0 X1 X2]
  have l4 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← h54075 X0 sK2 (sK1 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l7 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l1 sK0 X0 X1 sK1]
  have l8 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l9 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ X0)))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ X0))]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l8 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ X0) X3]
  have l11 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l9 X1 sK1 sK0 X0]
    conv => enter [1]; rw [← l6 X1 X0 sK0]
  have l12 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l10 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h54075 sK0 (sK1 ◇ sK0) sK1]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54075 sK0 X0 sK1]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54075 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h54075 sK0 sK0 sK1]
  have l16 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [h54075 sK0 X0 sK1]
  have l17 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) = (sK0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1]; rw [← l16 sK0 X0 X1 sK1]
  have l18 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54075 sK0 X0 sK1]
    conv => enter [1]; rw [l15 sK0 X0 sK1]
  have l19 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l17 X0 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h54075 sK0 sK1 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h54075 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l20 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
    conv => enter [1, 1]; rw [l13 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l18 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l28 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK2]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54075 sK0 sK1 sK1]
    conv => enter [1]; rw [l26 sK1 sK0]
  have l30 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l18 X0 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0 X0]
  have l31 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l28 sK1 sK0 sK2]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l32 sK1 sK0]
  have l36 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ (sK1 ◇ sK0)) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l33 sK0 sK1]
  have l37 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l36 sK1 sK0 X0]
    conv => enter [1]; rw [← l11 X0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l38 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0 X0]
  have l39 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l35 sK1 sK0]
  have l40 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK0 sK2]
    conv => enter [1]; rw [← l39 sK2 sK1 sK0]
  have l41 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1]; rw [l40 sK1 sK0 sK2]
  have l42 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 1]; rw [l41 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
    conv => enter [1]; rw [l21 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l14 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l43 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1 sK0]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l51 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l55 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l57 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [l55 X0 sK0 sK1]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l54 sK1 sK0]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ sK0)]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [l60 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l63 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l58 sK1 sK0]
  have l64 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54075 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l63 sK0 sK1 X0]
  have l65 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l62 sK1 sK0]
  have l66 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l57 X0 sK0 sK1]
    conv => enter [1]; rw [← l64 sK1 sK0 X0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l65 sK1 sK0]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54075 (sK0 ◇ (sK1 ◇ sK0)) X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l68 sK0 sK1]
  have l70 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l38 X0 sK1 sK0]
    conv => enter [1]; rw [← l69 sK0 sK1 X0]
  have l71 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l57 X0 sK0 sK1]
    conv => enter [1]; rw [← l70 X0 sK1 sK0]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
  have l73 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l61 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l74 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l73 sK1 sK0 X0]
  have l75 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [← l66 (sK1 ◇ sK0) sK0 sK1]
  have l76 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l58 sK1 sK0]
    conv => enter [1]; rw [← l75 sK1 sK0]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l76 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l71 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l79 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l41 sK2 sK1 sK0]
    conv => enter [1]; rw [← l71 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l78 sK1 sK0]
  have l81 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [h54075 (sK1 ◇ sK0) X0 sK0]
  have l82 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h54075 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 X1]
    conv => enter [1, 2]; rw [← h54075 (sK1 ◇ sK0) X0 sK0]
  have l83 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l82 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l84 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l81 sK0 sK1 X0]
    conv => enter [1]; rw [← l19 X0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l85 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l83 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l56 sK0 sK1 ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))]
  have l86 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l38 X0 sK1 sK0]
    conv => enter [1]; rw [← l84 sK0 sK1 X0]
  have l87 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l74 sK1 sK0 (X0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l85 X0 X1 sK0 sK1]
  have l88 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l71 X0 sK0 sK1]
    conv => enter [1]; rw [l86 X0 sK1 sK0]
  have l89 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 X0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l87 sK1 sK0 X0 sK0]
  have l90 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l66 X0 sK0 sK1]
    conv => enter [1]; rw [← l89 sK0 X0 sK1]
  have l91 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l90 sK1 sK0 X0]
    conv => enter [1]; rw [← l19 X0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l92 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l38 X0 sK1 sK0]
    conv => enter [1]; rw [← l91 sK1 sK0 X0]
  have l93 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l71 X0 sK0 sK1]
    conv => enter [1]; rw [l92 X0 sK1 sK0]
  have l94 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l95 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l77 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l96 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK0 sK2]
    conv => enter [1]; rw [l95 sK2 sK1 sK0]
  have l97 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l30 sK2 sK1 sK0]
    conv => enter [1]; rw [l96 sK1 sK0 sK2]
  have l98 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l88 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK1]
    conv => enter [1, 2]; rw [← l97 sK2 sK1 sK0]
  have l99 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l79 sK2 sK1 sK0]
    conv => enter [1]; rw [l98 sK2 sK1 sK0]
  have l100 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l99 sK2 sK1 sK0]
  have l101 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l94 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l100 sK1 sK0 sK2]
  have l102 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l99 sK2 sK1 sK0]
    conv => enter [1]; rw [l101 sK0 sK1 sK2]
  have l103 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l79 sK2 sK1 sK0]
    conv => enter [1]; rw [l93 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK1]
    conv => enter [1, 2]; rw [← l79 sK2 sK1 sK0]
  have l104 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l103 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l105 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l103 sK2 sK1 sK0]
  have l106 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l99 sK2 sK1 sK0]
    conv => enter [1]; rw [l105 sK0 sK1 sK2]
  have l107 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l102 sK2 sK1 sK0]
    conv => enter [1]; rw [l104 sK1 sK2 sK0]
  have l108 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 1]; rw [l106 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l109 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l107 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l110 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [l109 sK2 sK1 sK0]
  have l111 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l110 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l112 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l31 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l109 sK2 sK1 sK0]
  have l113 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) = ((sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [← h54075 (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0 X0]
    conv => enter [1, 2]; rw [← l31 sK1 sK0 sK2]
  have l114 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l113 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l115 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l112 sK1 sK0 sK2]
    conv => enter [1]; rw [← l108 sK2 sK1 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l116 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l114 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [l111 sK2 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l117 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [l115 sK1 sK0 sK2]
  have l118 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l116 sK0 X0 sK2 sK1]
    conv => enter [1, 2]; rw [l4 sK2 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l119 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [l117 sK1 sK0 sK2]
  have l120 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l118 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← l42 sK2 sK1 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l121 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l120 sK0 sK2 sK2 sK1]
    conv => enter [1]; rw [← l12 sK2 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK2]
  have l122 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l31 sK1 sK0 sK2]
    conv => enter [1]; rw [← l121 sK2 sK1 sK0]
  have l123 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l119 sK0 sK1 sK2]
    conv => enter [1]; rw [← l122 sK2 sK1 sK0]
  have l124 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l123 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0))]
  have l125 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l124 sK0 sK1 sK2]
    conv => enter [1]; rw [← l71 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK1]
  have l126 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l125 sK0 sK1 sK2]
    conv => enter [1]; rw [← l79 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l126 x y z]

end Semigroup5
