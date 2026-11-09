import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54031_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54031 : Equation54031 G) : Equation53816 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l8 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l13 sK1 X0]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l17 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l18 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l17 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l19 sK1]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← h54031 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l14 sK1 X0]
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ X0)]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l24 sK1 X0]
    conv => enter [1]; rw [← h54031 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ X0)]
  have l27 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l23 sK0 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ X0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ X0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l29 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l30 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l37 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l38 : ∀ sK0 X0 X1 : G, (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54031 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54031 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l36 sK0]
    conv => enter [1]; rw [h54031 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← l36 sK0]
  have l41 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h54031 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l42 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54031 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54031 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l20 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54031 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l21 sK0 sK1]
  have l45 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← h54031 (sK1 ◇ sK1) X0 sK1]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h54031 sK0 X0 (sK0 ◇ sK0)]
  have l47 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l14 sK1 X0]
    conv => enter [1]; rw [← h54031 sK1 X0 (sK1 ◇ sK1)]
  have l48 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54031 sK0 X0 sK0]
  have l49 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54031 sK0 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ X0)]
  have l50 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 (X1 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54031 sK0 X0 X1]
  have l51 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54031 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l52 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h54031 sK1 X0 sK1]
  have l53 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) = (sK1 ◇ (sK1 ◇ (X0 ◇ sK1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X1 ◇ (sK1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54031 sK1 X0 X1]
  have l54 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [← h54031 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l55 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l37 sK0 X0]
    conv => enter [1]; rw [l54 sK0 X0]
  have l56 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (X1 ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l53 sK1 X1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l57 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1]; rw [l52 sK1 X0]
  have l58 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [l51 sK0 X0 X1]
  have l59 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ X0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l50 sK0 X1 X0]
    conv => enter [1]; rw [← l10 sK0 (X0 ◇ sK0)]
  have l60 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l48 sK0 X0]
  have l61 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l25 sK1 X0]
    conv => enter [1]; rw [l45 sK1 X0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l25 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l44 sK1 sK0]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← l47 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l64 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l41 sK1 X0]
  have l65 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [l40 sK0 X0]
  have l66 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l39 sK0 sK1 X0]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK0)]
  have l67 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l46 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [l38 sK0 X0 X1]
  have l68 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ sK0)]
    conv => enter [1]; rw [l55 sK0 X0]
  have l69 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l59 sK0 sK0 X0]
  have l70 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l57 sK1 X0]
    conv => enter [1]; rw [l61 sK1 X0]
  have l71 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l62 sK1 sK0]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l47 sK1 sK1]
    conv => enter [1]; rw [l63 sK1 sK0]
  have l73 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l64 sK1 sK1]
    conv => enter [1]; rw [l56 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l66 sK0 sK0 sK1]
  have l75 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l12 sK0 X0]
    conv => enter [1]; rw [l67 sK0 X0 X1]
  have l76 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l65 sK0 X0]
    conv => enter [1]; rw [← l68 sK0 X0]
  have l77 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l60 sK0 X0]
    conv => enter [1]; rw [l69 sK0 X0]
  have l78 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0]
    conv => enter [1]; rw [← l70 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l79 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l72 sK1 sK0]
  have l80 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l25 sK1 sK1]
    conv => enter [1]; rw [← l73 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54031 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l74 sK0 sK1]
  have l82 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l75 sK0 X0 X1]
  have l83 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l77 sK0 X0]
    conv => enter [1, 2]; rw [← l76 sK0 X0]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [l78 sK1 sK0]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l79 sK1 sK0]
  have l86 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l80 sK1]
  have l87 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l37 sK0 X0]
    conv => enter [1]; rw [l82 sK0 X0 X1]
  have l88 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l85 sK1 sK1]
    conv => enter [1, 2]; rw [← l84 sK1 sK1]
  have l89 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l86 sK1]
  have l90 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l87 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l83 sK0 X0]
  have l91 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l88 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l92 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54031 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l90 sK0 X0 sK0]
  have l93 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l46 sK0 sK0]
    conv => enter [1]; rw [l92 sK0 X0]
  have l94 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l93 sK0 X0]
  have l95 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l94 sK0 X0]
  have l96 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l89 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l97 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54031 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l96 sK0 sK1]
  have l98 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l96 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l99 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l97 sK0 sK1 X0]
    conv => enter [1]; rw [← l98 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l100 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l91 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l101 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l89 sK1]
    conv => enter [1]; rw [← l100 sK1]
  have l102 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h54031 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l103 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l101 sK1]
    conv => enter [1]; rw [l102 sK1 X0]
  have l104 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54031 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l105 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [l104 sK0 sK1]
    conv => enter [1]; rw [← h54031 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) X0]
  have l106 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l105 sK0 sK1 X0]
    conv => enter [1]; rw [l99 sK0 sK1 (sK0 ◇ sK0)]
  have l107 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) X0]
  have l108 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l107 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK0 X0]
  have l109 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l108 sK0 X0 sK0]
    conv => enter [1]; rw [← l58 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l110 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l95 sK0 X0]
    conv => enter [1]; rw [← l109 sK0 X0]
  have l111 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l110 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l112 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l103 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l110 sK0 (sK1 ◇ sK1)]
  have l113 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54031 sK0 sK0 sK0]
    conv => enter [1]; rw [l111 sK0 sK1]
  have l114 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l112 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l115 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l114 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l83 sK0 X0]
  have l116 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l115 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h54031 sK0 sK0 sK0]
  have l117 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l112 sK1 sK1]
    conv => enter [1]; rw [← l116 sK1 X0 sK1]
  have l118 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [← h54031 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK0 X0]
  have l119 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l118 sK0 sK1 X0]
  have l120 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l119 sK0 sK1 sK0]
    conv => enter [1]; rw [l106 sK0 sK1 sK0]
  have l121 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l120 sK0 sK1]
  have l122 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l35 sK0 sK1]
    conv => enter [1]; rw [l121 sK0 sK1]
  have l123 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l113 sK0 sK1]
    conv => enter [1]; rw [l122 sK0 sK1]
  have l124 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l117 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l125 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l123 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l126 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l124 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)]
    conv => enter [1]; rw [← l125 sK0 X0 sK1]
  have l127 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l110 sK0 sK0]
    conv => enter [1]; rw [← l126 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l127 x y]

theorem Equation4512_54050_implies_Equation54013 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54050 : Equation54050 G) : Equation54013 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
    conv => enter [1]; rw [h54050 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54050 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [l2 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_54021_implies_Equation54020 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54021 : Equation54021 G) : Equation54020 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l5 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54021 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54021 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54021 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54021 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54021 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h54021 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK1 X0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l21 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l32 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l31 sK1 sK0 X0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l32 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1, 2]; rw [← l24 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l29 sK0 sK1 (sK0 ◇ sK0)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l46 x y]

theorem Equation4512_54087_implies_Equation54039 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54039 G := by
  have l0 : ∀ X2 sK2 sK1 X0 : G, (X2 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X2 sK2 sK1 X0
    conv => enter [1]; rw [← h54087 sK2 X2 X2 sK1]
    conv => enter [1]; rw [h54087 sK2 X2 X0 sK1]
  have l1 : ∀ X0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l0 X0 sK2 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [l1 X0 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK1 sK0]
  have l3 : ∀ sK0 sK2 sK1 X1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X1
    conv => enter [1]; rw [l2 sK0 sK2 sK1 X1 sK0]
  have l4 : ∀ X1 sK2 sK1 X2 sK0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X2))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X1 sK2 sK1 X2 sK0
    conv => enter [1]; rw [← h54087 (sK2 ◇ (sK2 ◇ sK1)) X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 sK1 sK0]
  have l5 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1)) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X1) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ (sK2 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [l0 X0 sK2 sK1 sK0]
  have l6 : ∀ sK0 sK2 sK1 X1 X2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X2))) := by
    intro sK0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l3 sK0 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l4 X1 sK2 sK1 X2 sK0]
  have l7 : ∀ sK0 sK2 sK1 X2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X2)) := by
    intro sK0 sK2 sK1 X2
    conv => enter [1]; rw [l6 sK0 sK2 sK1 sK0 X2]
    conv => enter [1]; rw [l5 sK0 sK2 sK1 ((sK2 ◇ (sK2 ◇ sK1)) ◇ X2) sK0]
  have l8 : ∀ sK0 sK2 sK1 X2 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X2) := by
    intro sK0 sK2 sK1 X2
    conv => enter [1]; rw [l7 sK0 sK2 sK1 X2]
    conv => enter [1]; rw [l5 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK2 sK1 X2 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54087 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_54087_implies_Equation54075 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54075 G := by
  have l0 : ∀ X2 sK2 sK0 X0 : G, (X2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro X2 sK2 sK0 X0
    conv => enter [1]; rw [← h54087 sK2 X2 X2 sK0]
    conv => enter [1]; rw [h54087 sK2 X2 X0 sK0]
  have l1 : ∀ X0 sK2 sK0 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 X1 X2
    conv => enter [1]; rw [l0 X0 sK2 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ (sK2 ◇ sK0))]
  have l2 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [l1 X0 sK2 sK0 X1 X0]
    conv => enter [1, 2]; rw [l0 X0 sK2 sK0 sK1]
  have l3 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X1 sK1]
  have l4 : ∀ X1 sK2 sK0 X2 sK1 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X1 sK2 sK0 X2 sK1
    conv => enter [1]; rw [← h54087 (sK2 ◇ (sK2 ◇ sK0)) X1 X1 X2]
    conv => enter [1, 2]; rw [l0 X1 sK2 sK0 sK1]
  have l5 : ∀ X0 sK2 sK0 X1 sK1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X1)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK2 sK0 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ (sK2 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l0 X0 sK2 sK0 sK1]
  have l6 : ∀ sK1 sK2 sK0 X1 X2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2))) := by
    intro sK1 sK2 sK0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [← l4 X1 sK2 sK0 X2 sK1]
  have l7 : ∀ sK1 sK2 sK0 X2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2)) := by
    intro sK1 sK2 sK0 X2
    conv => enter [1]; rw [l6 sK1 sK2 sK0 sK1 X2]
    conv => enter [1]; rw [l5 sK1 sK2 sK0 ((sK2 ◇ (sK2 ◇ sK0)) ◇ X2) sK1]
  have l8 : ∀ sK1 sK2 sK0 X2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X2) := by
    intro sK1 sK2 sK0 X2
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X2]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2 sK0 X2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54087 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_54087_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_54087_implies_Equation54048 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation54048 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h54087 sK0 sK1 X0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y y]

theorem Equation4512_54087_implies_Equation53827 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53827 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h54087 sK0 (sK0 ◇ sK0) X0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2))) := by
    intro sK0 X1 X2
    conv => enter [1, 2]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [h54087 (sK0 ◇ (sK0 ◇ sK0)) sK0 X1 X2]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l7 : ∀ sK0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 sK0 X2]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l4 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l9 : ∀ sK0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 X2]
    conv => enter [1]; rw [← l6 sK0 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l8 X0 X1 sK0 sK0]
  have l11 : ∀ sK0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X2]
  have l12 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l11 sK0 X2]
  have l13 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X2]
  have l14 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 X2 X0 X1
    conv => enter [1, 1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l15 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l14 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l16 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l13 sK0 X2]
    conv => enter [1]; rw [l15 sK0 X2 X0 X1]
  intro x y z
  conv => enter [1]; rw [l16 x y x z]

theorem Equation4512_54087_implies_Equation53844 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53844 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK2) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 sK0]
    conv => enter [1]; rw [h54087 sK0 sK2 X0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0 X0]
  have l4 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l3 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l4 X0 X1 sK0 sK0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK2 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l5 sK0 sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_54087_implies_Equation53824 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53824 G := by
  have l0 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_54087_implies_Equation53855 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53855 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h54087 sK1 sK1 X0 sK1]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 X0]
  have l3 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [l2 X0 X1 X2 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [← l3 X0 X1 sK1 sK1]
  have l5 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l4 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]

theorem Equation4512_54087_implies_Equation53848 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53848 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 X1 sK0 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_54087_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53826 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 X1 sK0 sK0]
  have l5 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l4 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y
  conv => enter [1]; rw [l5 x y x y]

theorem Equation4512_54087_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53833 G := by
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
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [h54087 sK0 (sK0 ◇ sK0) X0 sK0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [h54087 sK0 sK1 X0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK1 sK0 X1 X2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X2))) := by
    intro sK1 sK0 X1 X2
    conv => enter [1, 2]; rw [h54087 sK1 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h54087 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X1 X2]
  have l14 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [h54087 sK1 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) X1]
  have l15 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54087 sK1 sK0 (X0 ◇ X1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h54087 sK1 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h54087 sK1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54087 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54087 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l20 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l15 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h54087 sK1 sK0 sK1 (sK0 ◇ sK1)]
  have l21 : ∀ sK1 sK0 X2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X2)) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l13 sK1 sK0 sK1 X2]
    conv => enter [1]; rw [← l14 sK1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X2) sK1]
  have l22 : ∀ sK1 sK0 X2 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X2) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l21 sK1 sK0 X2]
    conv => enter [1]; rw [← l14 sK1 sK0 X2 (sK1 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK1 sK0 X2 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X2) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l20 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l22 sK1 sK0 X2]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1 (sK0 ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ sK1)]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2]; rw [← l30 sK1 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l33 sK1 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [l34 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l35 x y]

theorem Equation4512_54087_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53823 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54087 sK0 sK0 X0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y]

theorem Equation4512_54087_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54087 : Equation54087 G) : Equation53836 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [h54087 sK1 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [h54087 X0 X1 X2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l4 : ∀ X0 X1 X2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 X2 sK1
    conv => enter [1]; rw [l3 X0 X1 X2 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 X0]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 sK1]
    conv => enter [1]; rw [← l4 X0 X1 sK1 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_54048_implies_Equation54021 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54048 : Equation54048 G) : Equation54021 G := by
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
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0 X1]
    conv => enter [1, 2, 2]; rw [h54048 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1, 2]; rw [l13 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0 X0]
    conv => enter [1, 2, 2]; rw [← l3 X0 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X1 X0]
    conv => enter [1, 2]; rw [← l10 X0 X1 X1]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [← h54048 X1 X0]
    conv => enter [1]; rw [← l3 X1 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l3 X0 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l12 X1 X0 X0 X1]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [← l21 X1 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1, 2]; rw [l22 X1 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l18 X0 X1]
    conv => enter [1, 2, 2]; rw [h54048 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [l18 X1 X0]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l18 X0 X1]
    conv => enter [1]; rw [← l10 X1 X0 (X1 ◇ (X0 ◇ X1))]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l22 X1 X0]
    conv => enter [1]; rw [l26 X0 X1]
  have l28 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1]; rw [l15 X1 X0]
  have l29 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [l23 X1 X0]
    conv => enter [1]; rw [l27 X0 X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1]; rw [← l18 X0 X1]
  have l31 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l30 X0 X1]
    conv => enter [1]; rw [l22 X1 X0]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2, 2]; rw [← l30 X0 X1]
  have l33 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l32 X1 X0]
    conv => enter [1]; rw [← l29 X1 X0]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l32 X1 X0]
    conv => enter [1]; rw [← l16 X1 X0]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1, 2]; rw [← l34 X0 X1]
  intro x y
  conv => enter [1]; rw [l35 x y]
  conv => enter [1]; rw [l33 x y]
  conv => enter [1]; rw [← l31 x y]

theorem Equation4512_54048_implies_Equation54050 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54048 : Equation54048 G) : Equation54050 G := by
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
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h54048 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l11 X0 X1]
    conv => enter [1, 2]; rw [l12 X0 X1]
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
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1]; rw [l10 X1 X0 (X0 ◇ X1)]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l18 X1 X0]
    conv => enter [1]; rw [l13 X1 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l20 X0 X1]
    conv => enter [1]; rw [← l15 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1, 2, 2]; rw [← l21 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2, 2]; rw [← l21 X1 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [l23 X0 X1]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [← l25 X0 X1]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2]; rw [← l26 X1 X0]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l21 X1 X0]
  intro x y
  conv => enter [1]; rw [l28 x y]
  conv => enter [1]; rw [l27 y x]

theorem Equation4512_54048_implies_Equation54023 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54048 : Equation54048 G) : Equation54023 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54048 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54048 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X1 X0]
    conv => enter [1, 2]; rw [← l6 X0 X1 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← l8 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l11 X1 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]
  conv => enter [1]; rw [h54048 y x]

theorem Equation4512_54048_implies_Equation4321 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54048 : Equation54048 G) : Equation4321 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54048 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54048 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54048 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X1 X0]
    conv => enter [1, 2]; rw [← l6 X0 X1 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [← l8 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h54048 X0 X1]
    conv => enter [1]; rw [← l11 X1 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation54034_implies_Equation54013 (G : Type*) [Magma G] (h54034 : Equation54034 G) : Equation54013 G := by
  intro x y
  conv => enter [1]; rw [h54034 x y x]

@[equational_result]
theorem Equation54034_implies_Equation54023 (G : Type*) [Magma G] (h54034 : Equation54034 G) : Equation54023 G := by
  intro x y
  conv => enter [1]; rw [h54034 x y y]

@[equational_result]
theorem Equation54034_implies_Equation53812 (G : Type*) [Magma G] (h54034 : Equation54034 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h54034 x x y]

@[equational_result]
theorem Equation54026_implies_Equation54020 (G : Type*) [Magma G] (h54026 : Equation54026 G) : Equation54020 G := by
  intro x y
  conv => enter [1]; rw [h54026 x y x]

theorem Equation4512_54026_implies_Equation54023 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54026 : Equation54026 G) : Equation54023 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54026 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54026 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_54026_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54026 : Equation54026 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54026 sK0 sK0 X0]
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

theorem Equation4512_54023_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54023 : Equation54023 G) : Equation53807 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54023 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation4512_53854_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53828 G := by
  have l0 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK2]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y x z]

theorem Equation4512_53854_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53846 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z y]

theorem Equation4512_53854_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53850 G := by
  have l0 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK2]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z z]

theorem Equation4512_53854_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53818 G := by
  have l0 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK2]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x x y z]

theorem Equation4512_53854_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53825 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y x y]

theorem Equation4512_53854_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53838 G := by
  have l0 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK2]
  have l1 : ∀ sK0 X0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y y z]

@[equational_result]
theorem Equation53854_implies_Equation53842 (G : Type*) [Magma G] (h53854 : Equation53854 G) : Equation53842 G := by
  intro x y z
  conv => enter [1]; rw [h53854 x y z x]

theorem Equation4512_53854_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x x x y]

@[equational_result]
theorem Equation53854_implies_Equation53812 (G : Type*) [Magma G] (h53854 : Equation53854 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h53854 x x y x]

@[equational_result]
theorem Equation53854_implies_Equation53832 (G : Type*) [Magma G] (h53854 : Equation53854 G) : Equation53832 G := by
  intro x y
  conv => enter [1]; rw [h53854 x y y x]

theorem Equation4512_53854_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53815 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x x y y]

theorem Equation4512_53854_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53835 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53854 sK0 X0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y y]

theorem Equation4512_53854_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53822 G := by
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
  have l10 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53854 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53854 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [h53854 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l17 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l11 sK0]
  have l18 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53854 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l19 sK0]
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l20 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53854 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l23 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation4512_53854_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53854 sK0 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53854 (sK0 ◇ sK0) X0 X1 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53854 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 sK0]
    conv => enter [1]; rw [← l13 sK0]
  intro x
  conv => enter [1]; rw [l14 x]

theorem Equation4512_53821_implies_Equation53814 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53814 G := by
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
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK1 sK0 sK2 X0 X1 : G, (((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ sK2) ◇ X0) X1]
  have l9 : ∀ sK1 sK0 sK2 X0 X1 : G, (((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l8 sK1 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l10 : ∀ sK1 sK0 sK2 X0 X1 : G, (((sK1 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l9 sK1 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h53821 sK1 (sK0 ◇ sK2) X0 X1]
  have l11 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l10 sK1 sK0 sK2 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) sK0 X0 X1]
  have l15 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1, 2]; rw [l7 sK0]
  have l17 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l17 sK0 X0 X1]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ sK2)]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l7 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l20 sK0]
  have l22 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l11 sK1 sK0 sK2 X0 X1]
  have l23 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2 X0 X1]
  have l24 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 sK1 sK2 X0 X1]
  have l25 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X0 X1]
  have l26 : ∀ sK0 X2 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro sK0 X2 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l25 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) (X0 ◇ X1) X2]
  have l27 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l25 sK0 sK0 sK0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [← l26 sK0 X2 sK0 sK0 sK0 sK0]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) X0 X0]
    conv => enter [1, 2]; rw [← l25 sK0 X0 X0 X0 X0]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53821 sK0 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ X1)]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK0]
  have l31 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← h53821 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l28 X0 sK0]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK0 sK0]
  have l34 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l35 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l36 sK0]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [← l31 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l38 x y z]

theorem Equation4512_53821_implies_Equation53819 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53819 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) ◇ X1) = (sK1 ◇ (((sK2 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK2 ◇ sK1) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53821 sK1 (sK2 ◇ sK1) X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 X1]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0 X1]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l8 sK0 sK1 sK2 X0 X1]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 sK0 sK0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l9 sK0 sK0 sK0 sK0 sK0 X2]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (X0 ◇ (X0 ◇ X0))) X0 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0 X0 X0 X0]
  have l13 : ∀ X0 X1 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK1 sK0
    conv => enter [1]; rw [← h53821 X0 X1 sK2 sK1]
    conv => enter [1]; rw [l12 X0 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53821_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53817 G := by
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
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h53821 X1 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l6 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53821 sK0 X0 X1 X2]
  have l7 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 X0 X1 X2]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53821 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l16 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
    conv => enter [1, 2]; rw [← l18 sK0 (X0 ◇ X0)]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l19 X0 sK0]
    conv => enter [1]; rw [h53821 X0 sK1 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation4512_53821_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53818 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = (sK1 ◇ (((sK2 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK2 ◇ sK0) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK0) X0 X1]
  have l3 : ∀ sK1 sK2 sK0 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK0)) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h53821 sK1 (sK2 ◇ sK0) X0 X1]
  have l4 : ∀ sK1 sK2 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l3 sK1 sK2 sK0 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 X1]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0 X1]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l8 sK0 sK1 sK2 X0 X1]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 sK0 sK0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l9 sK0 sK0 sK0 sK0 sK0 X2]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) X0 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0 X0 X0 X0]
  have l13 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [← h53821 X0 X1 sK2 sK0]
    conv => enter [1]; rw [l12 X0 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53821_implies_Equation53813 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53813 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53821_implies_Equation53820 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53820 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (((sK2 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK2 ◇ sK2) ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK2) X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53821 sK1 (sK2 ◇ sK2) X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0 X1]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 X1]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0 X1]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [← l8 sK0 sK1 sK2 X0 X1]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 sK0 sK0 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l9 sK0 sK0 sK0 sK0 sK0 X2]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (X0 ◇ (X0 ◇ X0))) X0 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0 X0 X0 X0]
  have l13 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [← h53821 X0 X1 sK2 sK2]
    conv => enter [1]; rw [l12 X0 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53821_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53811 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK0 X0 X1]
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

theorem Equation4512_53821_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53821_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53812 G := by
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
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h53821 X1 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l6 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53821 sK0 X0 X1 X2]
  have l7 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 X0 X1 X2]
  have l8 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53821 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l16 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
    conv => enter [1, 2]; rw [← l18 sK0 (X0 ◇ X0)]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l19 X0 sK0]
    conv => enter [1]; rw [h53821 X0 sK1 sK0 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation4512_53821_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53821 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53821_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53815 G := by
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
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1, 2]; rw [l8 sK0]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l14 sK0 X0 X1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 (sK1 ◇ sK0)]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l8 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK0]
  have l18 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1 X0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0]
  have l23 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l22 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53821 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 sK1]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l31 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l33 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l35 sK0 X0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53821 X0 (sK0 ◇ (sK0 ◇ sK0)) X0 X0]
    conv => enter [1, 2]; rw [← l36 sK0 (X0 ◇ X0)]
  have l39 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l38 X0 sK0]
    conv => enter [1]; rw [h53821 X0 sK1 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [l39 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l40 x y]

theorem Equation4512_53821_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53816 G := by
  have l0 : ∀ sK1 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) = (sK1 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← h4512 sK1 ((sK1 ◇ sK1) ◇ X0) X1]
  have l1 : ∀ sK1 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK1) X0 X1]
  have l2 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53821 sK1 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l1 sK1 X0 X1]
  have l3 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l3 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l4 sK1 X0 X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l5 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53821 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 sK0 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_53821_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 X0 X1]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1, 2]; rw [l10 sK0]
  have l16 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l16 sK0 X0 X1]
  have l18 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK1) ◇ X0) X1]
  have l19 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l20 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) (sK0 ◇ sK1) X0 X1]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l20 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [l10 sK0]
  have l23 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l22 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 X1]
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ sK0) sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 X0]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l32 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l34 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53821 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK0 sK0 sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l41 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l40 sK0 X0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1 X0]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 sK0]
    conv => enter [1]; rw [← l41 sK0 X0 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l43 x y]

theorem Equation4512_53821_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53821 : Equation53821 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ X0) X1]
  have l10 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0 X1]
    conv => enter [1]; rw [← h53821 (sK0 ◇ sK0) sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 X0 X1]
    conv => enter [1]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X1) = (sK0 ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) X1]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X1) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l20 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 X1]
  have l22 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [h53821 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X1]
    conv => enter [1]; rw [← l21 sK0 X1 sK0]
  have l23 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X1
    conv => enter [1]; rw [l22 sK0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [← l19 sK0 sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l26 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l26 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l29 sK0 X0]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l30 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l31 sK0]
  intro x
  conv => enter [1]; rw [l32 x]

theorem Equation4512_53850_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53850 : Equation53850 G) : Equation53815 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53850 sK0 X0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation4512_53850_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53850 : Equation53850 G) : Equation53835 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53850 sK0 X0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation53850_implies_Equation53822 (G : Type*) [Magma G] (h53850 : Equation53850 G) : Equation53822 G := by
  intro x y
  conv => enter [1]; rw [h53850 x y x]

@[equational_result]
theorem Equation53850_implies_Equation53807 (G : Type*) [Magma G] (h53850 : Equation53850 G) : Equation53807 G := by
  intro x
  conv => enter [1]; rw [h53850 x x x]

theorem Equation4512_53817_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53817 : Equation53817 G) : Equation53815 G := by
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
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h53817 X1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53817 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (X0 ◇ X1))]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h53817 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53817 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l11 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h53817 (sK0 ◇ (sK0 ◇ sK0)) sK1 (sK1 ◇ sK0)]
  have l18 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK0]
  have l19 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [← l16 X1 sK0 X0]
    conv => enter [1]; rw [h53817 X1 sK1 sK0]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
    conv => enter [1]; rw [l17 sK0 X0 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [h53817 (sK0 ◇ (sK0 ◇ sK0)) sK1 (sK1 ◇ sK0)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53817 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l20 sK0 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation4512_53817_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53817 : Equation53817 G) : Equation53816 G := by
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
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h53817 X1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h53817 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (X0 ◇ X1))]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h53817 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l10 sK0 X0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h53817 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l11 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h53817 (sK0 ◇ (sK0 ◇ sK0)) sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l18 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK0]
  have l19 : ∀ X1 sK0 X0 sK1 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X1 sK0 X0 sK1
    conv => enter [1]; rw [← l16 X1 sK0 X0]
    conv => enter [1]; rw [h53817 X1 sK1 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [l3 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53817 (sK0 ◇ (sK0 ◇ sK0)) sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l18 sK0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53817 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK0]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation4512_53817_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53817 : Equation53817 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l4 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [h53817 X1 sK0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53817 X0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2]; rw [← h53817 sK0 X0 X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h53817 (sK0 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l2 sK0 sK1 (X0 ◇ (X0 ◇ X1))]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h53817 (sK0 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (X0 ◇ (X0 ◇ X1))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h53817 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h53817 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53817 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 X0 X1]
  have l12 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [l4 X1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53817 (sK0 ◇ sK0) sK0 sK0]
  have l16 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK0 sK1 X0
    conv => enter [1]; rw [← l12 X1 sK0 sK1 X0]
    conv => enter [1]; rw [h53817 X1 sK0 (sK0 ◇ sK1)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53817 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53817 (sK0 ◇ sK0) (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [h53817 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53817 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53817 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l30 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l29 sK0 X0 sK1]
    conv => enter [1]; rw [l16 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1 X0]
  have l31 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l30 sK0 X0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l31 sK0 X0 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l33 x y]

theorem Equation4512_53817_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53817 : Equation53817 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l9 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [← l13 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53817 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0 sK0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l18 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
  have l21 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l18 sK0 X0]
  have l22 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l21 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0 X1]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l24 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l22 sK0 X1 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 sK0]
  intro x
  conv => enter [1]; rw [l27 x]

theorem Equation4512_53848_implies_Equation53813 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53813 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53848 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53848_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53825 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53848 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53848_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53836 G := by
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
    conv => enter [1]; rw [h53848 X0 sK1 sK1]
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

theorem Equation4512_53848_implies_Equation4276 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation4276 G := by
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
    conv => enter [1]; rw [h53848 X0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1]; rw [← l2 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_53848_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53816 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53848 X0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53848 X0 X1 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 X1 sK0 sK1]
  have l7 : ∀ sK1 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK1 X1]
    conv => enter [1, 2]; rw [← l4 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l4 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53848_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53835 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53848 X0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l2 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h53848 X0 X1 X1]
    conv => enter [1, 2]; rw [l1 X1 sK1 sK0]
  have l3 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ X1) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h53848 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l1 X1 sK1 sK0]
  have l4 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X1) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l1 X0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l8 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l3 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l9 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [← l1 sK1 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 X1 sK1 sK0]
  have l10 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l7 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l8 X0 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 X0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 sK0]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l11 X0 X0 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l13 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l14 X0 X0 sK0]
    conv => enter [1]; rw [← l12 sK0 (X0 ◇ (X0 ◇ (X0 ◇ sK0)))]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l15 X0 sK0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l16 X0 X1 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l18 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation4512_53848_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53848 : Equation53848 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X3 ◇ (X4 ◇ (X3 ◇ X4))) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [← h53848 X0 X0 X1]
    conv => enter [1]; rw [h53848 X0 X3 X4]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53848 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53848 X0 X0 X0]
    conv => enter [1]; rw [← h53848 X1 X0 X0]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53848 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53848 X0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l13 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l12 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l14 X0 sK0]
    conv => enter [1, 2]; rw [l13 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 sK0 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  have l17 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h53848 X1 X1 X2]
    conv => enter [1]; rw [l11 X1 sK0 sK1]
  have l18 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l11 (X0 ◇ X1) sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l18 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l22 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [l17 X0 X1 sK0 sK1]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1, 2]; rw [l13 sK0 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l4 sK0]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l11 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l34 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [← h53848 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1 X2]
    conv => enter [1, 2]; rw [← l23 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l35 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l34 X1 X2 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l35 X1 X2 X1 sK0]
    conv => enter [1]; rw [← l23 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l8 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)]
  have l38 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l33 sK0 sK1 sK1]
    conv => enter [1]; rw [← l37 X0 X1 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l36 sK0 sK0 sK0]
    conv => enter [1]; rw [← l38 sK0 sK1 sK0 sK0]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l40 x y]

end Semigroup5
