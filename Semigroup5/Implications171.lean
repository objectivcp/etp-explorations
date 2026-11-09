import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41680_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41680 : Equation41680 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41680 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41680 (X1 ◇ X0) X1 X1]
    conv => enter [1, 2]; rw [← h41680 X0 X1 X1]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41680 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ X0))]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41680 X0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l6 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l5 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h41680 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41680 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [h41680 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41680 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [h41680 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l9 X0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1, 2]; rw [← l10 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41680 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l30 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l9 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l30 sK1 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1, 2]; rw [← l25 sK0]
  have l35 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l36 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l35 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l37 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l36 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l28 sK0 X1]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41680 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41680 (sK1 ◇ sK0) sK1 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l38 sK1 sK0]
  have l40 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h41680 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41680 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l41 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l43 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l45 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [h41680 X1 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l7 (X0 ◇ X1) sK1 sK0]
  have l46 : ∀ X1 X0 sK1 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 sK1 sK0
    conv => enter [1]; rw [l45 X1 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))))]
  have l47 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l46 X1 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l44 sK0 (X0 ◇ X1) X1]
  have l48 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l47 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l37 sK0 (X0 ◇ X1) X0]
  have l49 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l48 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l37 sK0 (X0 ◇ X1) X1]
  have l50 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l37 sK0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l49 X1 X0 sK0]
  have l51 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l8 X0 X0 sK0]
    conv => enter [1]; rw [← l40 sK0 X0 X0]
  have l52 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l50 sK0 X0 X1]
    conv => enter [1]; rw [l51 X1 sK0]
  have l53 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [← l50 sK0 X0 X1]
  have l54 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l53 X1 X2 sK0 X0]
  have l55 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← l52 sK0 (sK0 ◇ X1) X2]
    conv => enter [1]; rw [l54 sK0 sK0 X1 X2]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l55 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK0]
    conv => enter [1]; rw [← l56 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l57 x y]

@[equational_result]
theorem Equation315_implies_Equation41693 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation41693 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l3 sK2 sK1 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_41693_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41693 : Equation41693 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41693 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41693 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41693 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ (sK0 ◇ X0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X1 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41693 X0 sK0 X1]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41693 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41693 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41693 (sK1 ◇ sK0) sK1 sK1]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h41693 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK1 sK0 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l14 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
  have l15 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l14 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l15 X0 X1 sK0]
  have l17 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41693 X0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) sK1]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ X0)]
  have l20 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 X0 sK1]
    conv => enter [1]; rw [l17 X0 sK1 X0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation315_4512_implies_Equation41697 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41697 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ sK0) sK2]
  have l3 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK2 sK0]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1]; rw [← l3 sK2 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← h315 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l7 X0 sK0]
  have l9 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [l7 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l7 X0 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l12 X0 X1 sK0]
    conv => enter [1]; rw [l8 X0 X1 sK0]
  have l14 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l14 sK1 sK2 sK0 X0]
  have l16 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
    conv => enter [1]; rw [l16 sK2 sK0]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l17 sK2 sK0]
  have l19 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1]; rw [← l18 sK0 sK2]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l19 sK2 sK0]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1 sK2]
  have l23 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l20 sK0 sK0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l25 x y z]

theorem Equation4512_41697_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41697 : Equation41697 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41697 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41697 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1]; rw [← l4 sK0 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l7 X0 sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41697 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h41697 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l7 (sK1 ◇ sK0) sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l13 x y]

theorem Equation315_4512_implies_Equation41701 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41701 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [← h315 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [l0 sK1]
  have l2 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h315 (sK0 ◇ sK1) sK3]
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h315 (sK0 ◇ sK1) sK3]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h315 sK1 sK0]
  have l4 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h315 (sK0 ◇ sK1) sK3]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h315 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK3 sK0 sK1]
  have l6 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l5 sK3 sK0 sK1]
  have l7 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) = (sK2 ◇ ((sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h315 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) sK2]
    conv => enter [1, 2]; rw [← h315 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK2]
  have l8 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l6 sK3 sK0 sK1]
    conv => enter [1]; rw [← l7 sK2 sK3 sK0 sK1]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h315 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ X1 X0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l9 X0 sK1]
  have l11 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l6 sK3 sK0 sK1]
    conv => enter [1]; rw [l9 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK1]
  have l12 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l8 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l9 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) sK1]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 sK1]
  have l14 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l13 sK1 X0 X1]
  have l15 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l14 X0 X1 sK1]
    conv => enter [1]; rw [l10 X0 X1 sK1]
  have l16 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) X0]
  have l17 : ∀ sK1 X0 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [← l15 sK1 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [← l16 sK2 sK3 sK0 sK1 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l4 sK3 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l20 : ∀ sK1 sK0 sK3 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK3
    conv => enter [1]; rw [h315 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l19 sK3 sK0 sK1]
  have l21 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l20 sK1 sK0 sK3]
  have l22 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [← l21 sK3 sK0 sK1]
  have l23 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l6 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l24 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l23 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) sK2 sK3 sK0]
  have l25 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK3 sK0 sK1]
    conv => enter [1]; rw [← l24 sK2 sK3 sK0 sK1]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK1 sK1]
    conv => enter [1]; rw [l25 sK1 sK1 sK1 sK2]
    conv => enter [1, 2]; rw [← l22 sK1 sK1 sK1]
  have l27 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1, 2]; rw [l22 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l27 x y z w]

theorem Equation4512_41701_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41701 : Equation41701 G) : Equation315 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h41701 X0 X1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l2 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41701 X1 X2 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41701 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ X0)))]
  have l4 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41701 sK0 (X0 ◇ X1) X2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41701 sK0 sK0 sK0 sK0]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41701 sK0 (sK1 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK1 sK0 sK0]
  have l10 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l11 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = (X3 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l4 (X1 ◇ (X1 ◇ (X2 ◇ X0))) X3 X1 X1]
    conv => enter [1, 2]; rw [← h41701 X0 (X1 ◇ (X1 ◇ X1)) X1 X2]
  have l12 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ X1) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [h41701 X1 X1 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l4 ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) X1 sK1 sK0]
  have l13 : ∀ X0 X1 X2 sK1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 X2 sK1 sK0
    conv => enter [1]; rw [l4 X0 (X1 ◇ X2) sK1 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l14 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ X1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((X0 ◇ X1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l12 X1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (X0 ◇ X1) ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1))]
  have l15 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l11 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X2 ◇ X0)) (X1 ◇ (X1 ◇ (X2 ◇ X0)))]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X1 X1 X0]
    conv => enter [1]; rw [← l13 (X0 ◇ X1) (X1 ◇ (X1 ◇ X1)) (X0 ◇ X1) X1 X1]
  have l17 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ (X0 ◇ X0)) := by
    intro X0 X3
    conv => enter [1]; rw [l3 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l15 X3 X0 X0 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l19 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h41701 X0 X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l7 sK0 X0 X2]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 X0 X0]
  have l21 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) = (X2 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0 sK1 sK0]
    conv => enter [1]; rw [l17 X1 X2]
    conv => enter [1, 2]; rw [l4 X1 X0 sK1 sK0]
  have l22 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l17 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l22 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l24 : ∀ X0 X1 sK1 sK0 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X2)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X2) := by
    intro X0 X1 sK1 sK0 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X2]
    conv => enter [1, 1]; rw [← h41701 (sK1 ◇ sK0) X0 X1 sK1]
  have l25 : ∀ X0 X1 sK1 sK0 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X2)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X2)) := by
    intro X0 X1 sK1 sK0 X2
    conv => enter [1]; rw [l24 X0 X1 sK1 sK0 X2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X2]
  have l26 : ∀ sK0 X2 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X2)) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l10 sK0 X2 sK1]
    conv => enter [1]; rw [← l25 X0 X1 sK1 sK0 X2]
  have l27 : ∀ sK0 X2 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X2))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l26 sK0 X2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X2]
  have l28 : ∀ X0 X1 sK1 sK0 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2)))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X0 X1 sK1 sK0 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 (sK1 ◇ (sK1 ◇ sK0)) X2]
    conv => enter [1]; rw [← l27 sK0 X2 X0 X1 sK1]
  have l29 : ∀ X1 sK1 sK0 X2 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2))) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X1 sK1 sK0 X2
    conv => enter [1]; rw [l23 X1 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2) X1]
    conv => enter [1]; rw [l28 X1 X1 sK1 sK0 X2]
  have l30 : ∀ X1 sK1 sK0 X2 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X1 sK1 sK0 X2
    conv => enter [1]; rw [l21 X1 sK1 sK0 X2 X1]
    conv => enter [1]; rw [l29 X1 sK1 sK0 X2]
  have l31 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2]; rw [l4 X0 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK0]
    conv => enter [1]; rw [l30 X1 sK1 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l32 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l30 (sK0 ◇ sK0) sK0 sK0 X0]
    conv => enter [1]; rw [← l31 X1 X0 sK0 sK0]
  have l33 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l32 sK0 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l34 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X2 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l33 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← l18 X1 X0]
  have l35 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l34 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l32 sK0 X1 sK0]
  have l36 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) := by
    intro X0 X2 X1 sK0
    conv => enter [1, 1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X0) X2]
  have l37 : ∀ X0 X2 X1 sK0 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1 sK0
    conv => enter [1]; rw [l36 X0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X2]
  have l38 : ∀ X0 X2 sK0 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [l37 X0 X2 X0 sK0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ X2) X0]
  have l39 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← l35 sK0 X0 X2]
    conv => enter [1]; rw [← l38 X0 X2 sK0]
  have l40 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l39 sK0 X2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l40 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l41 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l42 x y]

theorem Equation315_4512_implies_Equation41721 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41721 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [← h315 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [l0 sK1]
  have l2 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h315 sK1 sK0]
    conv => enter [1]; rw [← h315 (sK1 ◇ sK1) sK3]
  have l3 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [← l2 sK3 sK0 sK1]
  have l4 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK3 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h315 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK3]
    conv => enter [1, 2]; rw [← l3 sK1 sK3 sK0]
  have l5 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [← h315 sK1 sK0]
    conv => enter [1]; rw [← l4 sK3 sK0 sK1]
  have l6 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = (sK2 ◇ ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h315 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK2]
    conv => enter [1, 2]; rw [← h315 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK2]
  have l7 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK3 sK0 sK1]
    conv => enter [1]; rw [← l6 sK2 sK3 sK0 sK1]
  have l8 : ∀ sK3 sK1 X0 sK0 : G, (sK3 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK3 sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK3 (sK1 ◇ sK1) X0]
    conv => enter [1, 1, 2]; rw [h315 sK1 sK0]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h315 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l10 : ∀ X1 X0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l9 X0 sK1]
  have l11 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l5 sK3 sK0 sK1]
    conv => enter [1]; rw [l9 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l12 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l9 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) sK1]
  have l13 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 sK1]
  have l14 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l13 sK1 X0 X1]
  have l15 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l14 X0 X1 sK1]
    conv => enter [1]; rw [l10 X0 X1 sK1]
  have l16 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0)) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l17 : ∀ sK1 X0 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [← l15 sK1 (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1]; rw [← l16 sK2 sK3 sK0 sK1 X0]
  have l18 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l19 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l18 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l17 sK1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK2 sK3 sK0]
  have l20 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK3 sK0 sK1]
    conv => enter [1]; rw [← l19 sK2 sK3 sK0 sK1]
  have l21 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1, 2]; rw [l11 sK3 sK0 sK1]
    conv => enter [1]; rw [l8 sK3 sK1 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l22 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [l5 sK3 sK0 sK1]
    conv => enter [1]; rw [← l21 sK3 sK0 sK1]
  have l23 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK3 sK0]
    conv => enter [1]; rw [← l22 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l23 x z w]
  conv => enter [1]; rw [l20 z w x y]

theorem Equation4512_41721_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41721 : Equation41721 G) : Equation315 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 X5 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1]; rw [h41721 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X3 X4 X5]
    conv => enter [1, 2, 2, 2]; rw [← h41721 X0 X5 X1 X2]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h41721 X0 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X2 ◇ (X3 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h41721 (X1 ◇ (X1 ◇ X0)) X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h41721 X0 X1 X1 X1]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X0))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41721 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X4 ◇ (X4 ◇ X0)))]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l2 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0))]
  have l5 : ∀ X3 X4 X5 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := by
    intro X3 X4 X5 X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X2 X0 X3 X4 X5]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X0)) (X1 ◇ (X2 ◇ (X2 ◇ X0)))]
  have l6 : ∀ X0 X2 X3 : G, (X0 ◇ X0) = (X2 ◇ (X3 ◇ (X0 ◇ X0))) := by
    intro X0 X2 X3
    conv => enter [1]; rw [h41721 X0 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l4 X2 X3 X0 X0]
  have l7 : ∀ X0 X3 X4 X5 : G, (X0 ◇ X0) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X0)))) := by
    intro X0 X3 X4 X5
    conv => enter [1]; rw [l3 X0 X0 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← l5 X3 X4 X5 X0 X0 X0]
  have l8 : ∀ X0 X3 : G, (X0 ◇ X0) = (X3 ◇ (X0 ◇ X0)) := by
    intro X0 X3
    conv => enter [1]; rw [l7 X0 X3 X0 X0]
    conv => enter [1, 2]; rw [← l6 X0 X0 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41721 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 X2 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ ((X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X2)) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1, 1]; rw [h41721 sK0 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X2]
  have l11 : ∀ sK0 X0 X1 X2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 sK1
    conv => enter [1]; rw [h41721 sK0 (X0 ◇ X1) X2 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41721 sK0 sK0 sK0 sK0]
  have l13 : ∀ sK0 X2 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l10 sK0 X2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK1 ◇ (sK1 ◇ sK0)) X2]
  have l14 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l15 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l17 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h41721 X0 X1 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l14 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) sK1]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l17 X0 X0 sK0 X0]
    conv => enter [1]; rw [← l13 sK0 X0 X0 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l18 X0 sK0]
    conv => enter [1]; rw [h41721 X0 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [l18 X0 sK0]
  have l20 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l1 X0 sK0 X0 sK0]
  have l21 : ∀ X3 X0 sK0 X1 X2 : G, (X3 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) := by
    intro X3 X0 sK0 X1 X2
    conv => enter [1, 2]; rw [h41721 X0 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X1 X2]
    conv => enter [1]; rw [← l20 sK0 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X3]
  have l22 : ∀ X3 X0 sK0 X2 : G, (X3 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X3 X0 sK0 X2
    conv => enter [1]; rw [l21 X3 X0 sK0 X3 X2]
    conv => enter [1, 2]; rw [← l16 X2 X0 X3]
  have l23 : ∀ X2 X0 X3 : G, (X2 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X3
    conv => enter [1]; rw [l16 X2 X0 (X2 ◇ X2)]
    conv => enter [1]; rw [← l22 X3 X0 X2 X2]
  have l24 : ∀ sK0 X0 X2 : G, ((sK0 ◇ sK0) ◇ X0) = (X2 ◇ (X2 ◇ X0)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l20 sK0 X0 sK0]
    conv => enter [1]; rw [← l23 X2 X0 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l24 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l26 x y]

theorem Equation316_4512_implies_Equation317 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation317 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation317_implies_Equation316 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h317 x y y]

@[equational_result]
theorem Equation316_implies_Equation320 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation320 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK2 X0]
  have l1 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
  have l2 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l3 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l2 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l5 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l3 sK2 X1 sK2 sK0]
  have l6 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l5 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK2]
  have l7 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l6 sK0 X1 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

@[equational_result]
theorem Equation320_implies_Equation316 (G : Type*) [Magma G] (h320 : Equation320 G) : Equation316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h320 sK0 sK0 sK0]
    conv => enter [1]; rw [← h320 sK1 sK0 sK0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h320 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation316_4512_implies_Equation3270 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3270 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l1 X2 sK0]
    conv => enter [1]; rw [l3 X2 X2 sK0]
  have l7 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X2) sK0]
  have l8 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 sK0 sK0]
  have l9 : ∀ X0 X2 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l8 sK0 X0 X2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation3270_implies_Equation316 (G : Type*) [Magma G] (h3270 : Equation3270 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3270 X1 X2 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h3270 X0 X1 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3270 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3270 X0 X0 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l1 X0 X1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3270 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3270 sK0 sK0 sK0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h3270 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h3270 sK1 sK1 sK1]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3270 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 X0 sK1]
    conv => enter [1]; rw [← l4 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]
  conv => enter [1]; rw [l4 y y]

@[equational_result]
theorem Equation316_implies_Equation3272 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3272 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ sK1) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK1]
  have l2 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [← l1 X1 sK1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation3272_4512_implies_Equation316 (G : Type*) [Magma G] (h3272 : Equation3272 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h3272 X1 X0]
    conv => enter [1]; rw [h3272 X1 X2]
  have l1 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h3272 X0 X1]
    conv => enter [1]; rw [h3272 X0 sK0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h3272 X0 sK0]
    conv => enter [1]; rw [h3272 X0 sK1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h3272 X0 X1]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3272 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3272 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [h3272 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l9 sK1]
  have l11 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1)))) = (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1))) := by
    intro X0 sK1 X1
    conv => enter [1, 2]; rw [← h3272 (X0 ◇ X0) sK1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ X0) X1]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l11 X0 sK1 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l12 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (sK1 ◇ sK1)]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 X0 sK1]
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ sK1) X0]
  have l15 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h3272 sK1 sK1]
    conv => enter [1]; rw [← l14 sK0 X0 sK1]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 sK1 X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (sK1 ◇ sK1)]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK0 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← h3272 (sK0 ◇ sK0) sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]
  conv => enter [1]; rw [l10 y]

@[equational_result]
theorem Equation316_implies_Equation3276 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3276 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK2 X0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h316 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  have l3 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
  have l4 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l5 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l4 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l3 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l7 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l5 sK2 X1 sK2 sK0]
  have l8 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l7 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK2]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 X1 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation3276_4512_implies_Equation316 (G : Type*) [Magma G] (h3276 : Equation3276 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h3276 X1 X2 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h3276 (X0 ◇ X0) X1 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X1 X0]
    conv => enter [1]; rw [← h3276 (X0 ◇ X0) X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h3276 X1 X1 X1]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h3276 (sK0 ◇ sK0) X1 sK0]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation316_4512_implies_Equation3279 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3279 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x y (x ◇ y)]

theorem Equation3279_4512_implies_Equation316 (G : Type*) [Magma G] (h3279 : Equation3279 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h3279 X0 X1]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h3279 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3279 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3279 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h3279 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [← l8 sK0]
  have l14 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [h3279 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3279 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l16 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l17 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3279 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h3279 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l14 sK1]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2, 2]; rw [l16 sK1]
    conv => enter [1]; rw [← h3279 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l20 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l19 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1]
    conv => enter [1]; rw [l20 sK1]
  have l22 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [← l14 sK1]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 X0 sK0]
    conv => enter [1]; rw [h3279 X0 X0]
    conv => enter [1, 2, 2]; rw [l9 X0 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l28 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l21 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]
  conv => enter [1]; rw [l22 y]

theorem Equation316_4512_implies_Equation3280 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3280 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y (x ◇ z)]

@[equational_result]
theorem Equation3280_implies_Equation316 (G : Type*) [Magma G] (h3280 : Equation3280 G) : Equation316 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3280 X0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h3280 sK0 X0 sK0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3280 X0 X1 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3280 sK0 X0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 X0 sK0]
    conv => enter [1]; rw [← h3280 sK0 X0 sK0]
  have l3 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l3 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation316_4512_implies_Equation3283 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3283 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [h316 X1 X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l3 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l1 X2 sK0]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l8 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l7 X1 X2 X0]
    conv => enter [1]; rw [l4 X0 (X0 ◇ X2) sK0]
  have l9 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l8 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l6 sK0 (X1 ◇ X2)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation3283_implies_Equation316 (G : Type*) [Magma G] (h3283 : Equation3283 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3283 X0 X0 X0]
    conv => enter [1]; rw [← h3283 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3283 X0 X1 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3283 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 X1]
  have l5 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l4 sK1 X1 sK0]
  have l6 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l5 sK0 X1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation316_4512_implies_Equation3285 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3285 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z
  conv => enter [1]; rw [l10 x y (z ◇ y)]

theorem Equation3285_4512_implies_Equation316 (G : Type*) [Magma G] (h3285 : Equation3285 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3285 X0 X0 X0]
    conv => enter [1]; rw [← h3285 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X1))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h3285 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3285 X0 X1 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l2 sK1 X1 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 X1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3285 sK0 sK1 sK1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = ((X1 ◇ (sK0 ◇ sK0)) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3285 X0 (X1 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l4 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l8 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [h3285 (sK0 ◇ sK0) sK1 sK1]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 X0]
  have l11 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l10 sK1 X1 sK0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0 X1 sK0]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h3285 X0 ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) X1]
    conv => enter [1, 2, 2]; rw [← l12 sK0 X1]
  have l14 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l14 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) (((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))]
  have l16 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l15 X0 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l16 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [l1 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK1 sK0 X1 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l17 sK1 sK0 X1]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 sK0 X1]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation316_4512_implies_Equation3287 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3287 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l4 sK1 sK1 sK1]
    conv => enter [1]; rw [← l3 X2 sK1 sK1]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l5 sK1 X2]
    conv => enter [1]; rw [l1 X2 X2 sK1]
  have l8 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK1]
  have l9 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK1 sK1]
  have l10 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l9 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  intro x y z w
  conv => enter [1]; rw [l10 x y (z ◇ w)]

theorem Equation3287_4512_implies_Equation316 (G : Type*) [Magma G] (h3287 : Equation3287 G) (h4512 : Equation4512 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3287 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3287 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = ((X1 ◇ X2) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h3287 X0 (X1 ◇ X2) X1 X2]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X2) sK0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l1 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 X1 X2 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 X2 sK0
    conv => enter [1]; rw [l2 sK1 X1 X2 sK0]
  have l4 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l3 sK0 X1 X2 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation316_implies_Equation3293 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3293 G := by
  have l0 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK1]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 sK0 X1]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 sK0]
    conv => enter [1, 2]; rw [l2 X0 sK0]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation3293_implies_Equation316 (G : Type*) [Magma G] (h3293 : Equation3293 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3293 X0 X0 X0]
    conv => enter [1]; rw [← h3293 X1 X0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3293 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation316_implies_Equation3298 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3298 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h316 sK2 sK2]
    conv => enter [1]; rw [h316 sK2 X0]
  have l1 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 X0]
    conv => enter [1, 2]; rw [h316 X0 sK2]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ sK2) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h316 sK2 sK2]
    conv => enter [1]; rw [l1 sK2 X0]
    conv => enter [1, 2]; rw [← h316 sK2 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [h316 sK0 sK2]
    conv => enter [1]; rw [← h316 sK2 sK2]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l2 sK2 sK1]
    conv => enter [1, 2]; rw [h316 sK2 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l4 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation3298_implies_Equation316 (G : Type*) [Magma G] (h3298 : Equation3298 G) : Equation316 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h3298 X0 X0 X0]
    conv => enter [1]; rw [← h3298 X1 X0 X0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X2))) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [← h3298 X1 X1 X2]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 X2 sK1 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X1 X2 sK1
    conv => enter [1]; rw [← l1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [l0 X2 sK1]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation316_4512_implies_Equation3299 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation3299 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

@[equational_result]
theorem Equation3299_implies_Equation316 (G : Type*) [Magma G] (h3299 : Equation3299 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3299 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3299 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h3299 X0 X1 X2 X2]
    conv => enter [1, 2, 2]; rw [l0 X2 sK0]
  have l2 : ∀ sK1 X1 X2 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK1 X1 X2 sK0
    conv => enter [1]; rw [l1 sK1 X1 X2 sK0]
  have l3 : ∀ sK0 X1 X2 : G, (sK0 ◇ sK0) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l2 sK0 X1 X2 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation316_implies_Equation3303 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation3303 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h316 sK1 sK1]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK1]
  have l3 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l2 sK1 X1 sK1]
  have l4 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l3 sK1 X1]
    conv => enter [1, 2]; rw [← l1 sK1]
  have l5 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK3]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1, 2]; rw [l5 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

@[equational_result]
theorem Equation3303_implies_Equation316 (G : Type*) [Magma G] (h3303 : Equation3303 G) : Equation316 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h3303 X1 X1 X1 X1]
    conv => enter [1]; rw [← h3303 X0 X1 X1 X1]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3303 X0 X1 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 (X0 ◇ X0) sK0]
  have l2 : ∀ sK1 X1 sK0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l1 sK1 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l2 sK0 X1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation316_4512_implies_Equation41582 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41582 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h316 sK0 sK0]
  have l2 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l2 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l2 X2 sK0]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

theorem Equation4512_41582_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41582 : Equation41582 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l7 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h41582 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2, 2]; rw [← h41582 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41582 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [h41582 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [l7 sK1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41582 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l16 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41582 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41582 X0 X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41582 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41582 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41582 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK1 X0]
  have l22 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l16 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l23 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1, 2, 2]; rw [l11 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h41582 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l26 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41582 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l28 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [← l9 sK1 sK1]
  have l29 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1, 2]; rw [l11 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l30 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l15 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l24 sK0]
  have l31 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l32 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l33 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l34 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l35 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [l4 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l36 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1, 2]; rw [← l30 sK0]
  have l37 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l33 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l38 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l34 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l39 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1, 2]; rw [← l22 (sK1 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l41 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2]; rw [← l18 X1 X0 X0]
  have l42 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l31 sK1]
    conv => enter [1]; rw [← l39 sK1]
  have l43 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l38 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l44 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l42 sK1]
    conv => enter [1]; rw [← l43 sK1]
  have l45 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
    conv => enter [1, 2]; rw [← h41582 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l46 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l45 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (X0 ◇ X0)]
  have l47 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l46 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (X0 ◇ X0)]
  have l48 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l47 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ X0)]
  have l49 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l48 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l41 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l50 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h41582 X0 X0]
    conv => enter [1]; rw [← l49 sK1 X0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0]
    conv => enter [1]; rw [l50 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l51 x y]
  conv => enter [1]; rw [l44 y]

theorem Equation316_4512_implies_Equation41583 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41583 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h316 sK0 sK0]
  have l2 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l2 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l2 X2 sK0]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ X0 X2 sK0 : G, (X0 ◇ (X0 ◇ X2)) = (sK0 ◇ sK0) := by
    intro X0 X2 sK0
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [← l9 sK0 X0 X2]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2]; rw [← l10 sK0 sK2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_41583_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41583 : Equation41583 G) : Equation316 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41583 sK1 X1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41583 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41583 X0 X0 X0]
  have l4 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41583 sK1 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X0 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41583 X0 X1 X2]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [← l5 X1 X0 X2 X3]
  have l7 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l4 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l1 sK1 X0]
  have l8 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l2 sK1 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41583 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X2)) X3]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) sK0]
  have l12 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l10 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X2) X3]
  have l13 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l8 sK1 X1 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 (sK1 ◇ sK1) sK1]
  have l14 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l12 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l15 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41583 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l14 X0 X3 X0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l15 (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l13 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l19 x y]
  conv => enter [1]; rw [l13 y y]

theorem Equation316_4512_implies_Equation41586 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41586 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l1 X2 sK0]
    conv => enter [1]; rw [l3 X2 X2 sK0]
  have l7 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l3 X1 (X1 ◇ X2) sK0]
  have l8 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 sK0 sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l8 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_41586_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41586 : Equation41586 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l4 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41586 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41586 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l9 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41586 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l10 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41586 X0 X1 X2]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41586 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK1 ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1, 2]; rw [l6 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l13 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l10 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l16 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l13 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1, 2]; rw [l6 sK1 X0]
  have l19 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l16 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l17 sK0 sK0]
  have l21 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l18 sK1 sK1]
  have l22 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l19 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l23 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41586 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l22 X0 X3 X0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l20 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l23 (sK0 ◇ sK0) X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l25 sK0 X0]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l29 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l21 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l30 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l29 sK1 X0]
    conv => enter [1]; rw [← l23 (sK1 ◇ sK1) X0]
  have l31 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l30 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l32 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [← l31 sK1 X0]
  have l33 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h41586 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l26 sK0 (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l34 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l28 sK1]
    conv => enter [1]; rw [l4 sK1]
  have l35 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l32 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l34 sK1]
  have l36 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h41586 X0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l32 sK1 (X0 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0)))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l37 x y]
  conv => enter [1]; rw [l35 y]

theorem Equation316_4512_implies_Equation41588 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41588 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK0 : G, (X1 ◇ X1) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X2
    conv => enter [1]; rw [l2 sK0 X2 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 X2 sK0 sK0]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l8 sK0 X2]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l11 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK0]
  have l12 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK0 sK0]
  have l13 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l12 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_41588_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41588 : Equation41588 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ X1 X0 X2 X3 : G, (X1 ◇ X1) = ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h41588 X1 (X0 ◇ (X0 ◇ (X2 ◇ X3))) X3]
    conv => enter [1, 2, 2, 2]; rw [← h41588 X0 X3 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = ((X0 ◇ (X2 ◇ X1)) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41588 X1 (X0 ◇ (X2 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h41588 X0 X1 X2]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41588 sK1 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41588 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41588 (sK1 ◇ (sK1 ◇ sK1)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← l9 sK1 X0]
  have l15 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41588 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l16 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41588 sK1 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l17 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41588 (sK1 ◇ sK1) X1 X0]
    conv => enter [1, 2]; rw [l4 sK1 (X0 ◇ X1)]
  have l18 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l17 sK1 X1 X0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l14 sK1 X0]
    conv => enter [1, 2]; rw [← l9 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l13 sK1 X0]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l22 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X0 ◇ ((X2 ◇ X1) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l11 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ X1) (X1 ◇ (X0 ◇ X0))]
  have l23 : ∀ X1 X0 X2 X3 : G, (X1 ◇ X1) = (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l10 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X2 ◇ X3)) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l24 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l19 sK1 sK1]
  have l25 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l20 sK1 sK1]
  have l26 : ∀ X1 X0 X2 : G, (X1 ◇ X1) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l22 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X1 (X1 ◇ (X0 ◇ X0))]
  have l27 : ∀ X1 X0 X2 X3 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l23 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X3) (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l28 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0 X1 X1]
    conv => enter [1, 2]; rw [← l26 X1 X0 (X1 ◇ X1)]
  have l29 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l25 sK1]
    conv => enter [1]; rw [← l9 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l30 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l25 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l31 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [← l28 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1]; rw [← l31 sK1]
  have l33 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l25 sK1]
    conv => enter [1]; rw [l32 sK1]
  have l34 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1]; rw [l7 sK1]
  have l35 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l34 sK1]
    conv => enter [1]; rw [← l30 sK1]
  have l36 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l21 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l21 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l39 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l36 sK1 X0 X1]
    conv => enter [1, 2, 2, 1]; rw [← l35 sK1]
  have l40 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l39 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l16 sK1 sK1 X0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l40 sK1 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l41 x y]
  conv => enter [1]; rw [l35 y]

@[equational_result]
theorem Equation316_implies_Equation41589 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41589 G := by
  have l0 : ∀ X0 sK2 : G, (X0 ◇ X0) = (sK2 ◇ sK2) := by
    intro X0 sK2
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK2 X0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h316 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h316 sK2 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK2 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h316 sK2 sK2]
  have l6 : ∀ X0 X1 sK2 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h316 X0 X1]
    conv => enter [1, 2]; rw [h316 X1 sK2]
  have l7 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l6 X0 X1 sK2]
    conv => enter [1, 2, 2]; rw [l0 sK2 sK0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l5 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  have l9 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l7 sK2 X1 sK2 sK0]
  have l10 : ∀ sK2 X1 sK0 : G, (sK2 ◇ sK2) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK2 X1 sK0
    conv => enter [1]; rw [l9 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK2]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 X1 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_41589_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41589 : Equation41589 G) : Equation316 G := by
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
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l5 sK1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l8 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41589 sK1 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l9 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41589 (sK1 ◇ sK1) X1 X0]
    conv => enter [1, 2]; rw [l3 sK1 (X0 ◇ X0)]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41589 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ X3)))]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41589 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (X0 ◇ X0))]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41589 X0 X0 X0]
  have l14 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 sK1 X1 X0]
  have l15 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l14 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [← l13 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l8 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l13 X0 (sK1 ◇ sK1)]
  have l17 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l13 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l12 sK1 X0]
  have l18 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l15 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l13 X0 sK1]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1 sK1]
    conv => enter [1]; rw [← l18 sK1 sK1 sK1]
  have l20 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l17 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← l5 sK1]
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1, 2]; rw [l5 sK1]
  have l22 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 sK1]
    conv => enter [1]; rw [← l13 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l23 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1, 1]; rw [l17 sK1 sK0]
  have l26 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l19 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1]
    conv => enter [1, 2]; rw [l17 sK1 sK0]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l28 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l29 x y]

theorem Equation316_4512_implies_Equation41590 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41590 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X1) = (X2 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h316 X1 X2]
    conv => enter [1, 2]; rw [l0 X2 X0]
  have l2 : ∀ X1 X2 sK1 : G, (X1 ◇ X1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l1 X1 X2 X1]
    conv => enter [1, 2]; rw [l0 X1 sK1]
  have l3 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X2
    conv => enter [1]; rw [l2 sK1 X2 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK1]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK1 X2
    conv => enter [1]; rw [l7 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 X2 sK1 sK1]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l10 : ∀ sK1 X2 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X2) := by
    intro sK1 X2
    conv => enter [1]; rw [l8 sK1 X2]
    conv => enter [1]; rw [l4 X2 X2 sK1]
  have l11 : ∀ X0 X2 sK1 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK1 ◇ sK1) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK1 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK1]
  have l12 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = ((X0 ◇ X0) ◇ X2) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ X2)]
    conv => enter [1]; rw [← l11 X0 X2 sK1 sK1]
  have l13 : ∀ sK1 X0 X2 : G, (sK1 ◇ sK1) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK1 X0 X2
    conv => enter [1]; rw [l12 sK1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2]
    conv => enter [1, 2]; rw [l13 sK1 sK1 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l14 x y z w]

theorem Equation4512_41590_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41590 : Equation41590 G) : Equation316 G := by
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
  have l4 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41590 sK1 X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41590 (sK1 ◇ sK1) X1 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l1 sK1 X0]
  have l6 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h41590 (sK1 ◇ sK1) X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [l3 sK1 X0]
  have l7 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ sK1) = (X2 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [h41590 sK1 X2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h41590 sK1 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (X0 ◇ X1))]
  have l9 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ X1)]
  have l10 : ∀ sK1 X1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l6 sK1 X1 X0]
    conv => enter [1, 2]; rw [← l1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l11 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l5 sK1 X1 X0]
  have l12 : ∀ sK1 X1 X0 : G, (sK1 ◇ sK1) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l4 sK1 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l13 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 X1 X0]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l11 sK1 sK1 sK1]
  have l15 : ∀ sK1 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l13 sK1 X1 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l16 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1]; rw [l15 sK1 X1]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l14 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 sK1 X0]
    conv => enter [1]; rw [← l17 sK1 X0]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h41590 X0 (sK1 ◇ sK1) X0 X0]
    conv => enter [1]; rw [← l18 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  intro x y
  conv => enter [1]; rw [l19 x y]
  conv => enter [1]; rw [l16 y y]

theorem Equation316_4512_implies_Equation41593 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41593 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l2 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← h316 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ X2)) := by
    intro sK0 X2
    conv => enter [1]; rw [l4 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 X2 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l5 sK0 X2]
    conv => enter [1]; rw [l1 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l1 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l11 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l10 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l12 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l11 sK0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l12 x y x z]

theorem Equation4512_41593_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41593 : Equation41593 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l4 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41593 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h41593 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X2))) X3]
    conv => enter [1, 1]; rw [← h41593 X0 X1 X2]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41593 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l12 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l9 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l8 sK1 X0]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l7 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← h41593 (sK0 ◇ sK0) sK0 sK0]
  have l16 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l12 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l14 sK1 X0]
  have l18 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l16 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1 sK1]
    conv => enter [1]; rw [← l17 sK1 sK1]
  have l20 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l13 sK1 sK1]
    conv => enter [1]; rw [← l14 sK1 sK1]
  have l21 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l18 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l22 : ∀ X0 X3 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X3
    conv => enter [1]; rw [h41593 X0 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l21 X0 X3 X0 X0]
  have l23 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l19 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ sK1)]
  have l25 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l20 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l26 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l25 sK1 X0]
    conv => enter [1]; rw [← l22 (sK1 ◇ sK1) X0]
  have l27 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← l4 sK1]
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1, 2]; rw [l4 sK1]
  have l28 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l26 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l22 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l27 sK1]
  have l30 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l28 sK1 X0]
  have l31 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1]; rw [← l29 sK1]
  have l32 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1]
    conv => enter [1]; rw [← l31 sK1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l22 (sK0 ◇ sK0) X0]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l34 sK0 X0]
  have l36 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h41593 X0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l30 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0)))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l36 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l37 x y]
  conv => enter [1]; rw [l32 y]

@[equational_result]
theorem Equation316_implies_Equation41595 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation41595 G := by
  have l0 : ∀ X1 sK1 : G, (X1 ◇ (X1 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro X1 sK1
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [h316 X1 sK1]
  have l1 : ∀ sK1 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X1
    conv => enter [1]; rw [l0 sK1 X1]
    conv => enter [1, 2]; rw [h316 X1 sK1]
  have l2 : ∀ sK1 X1 : G, (sK1 ◇ sK1) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X1
    conv => enter [1]; rw [h316 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X1]
    conv => enter [1, 2]; rw [← h316 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h316 sK0 sK1]
    conv => enter [1]; rw [← h316 sK1 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [h316 sK1 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_41595_implies_Equation316 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41595 : Equation41595 G) : Equation316 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK1 X0]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l7 sK1]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41595 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41595 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h41595 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h41595 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l2 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h41595 X0 sK1]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l16 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 sK1]
  have l18 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l15 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK1]
  have l19 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l14 sK1]
    conv => enter [1, 2]; rw [l11 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l12 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l23 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
  have l24 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [l4 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l26 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l23 sK1]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l27 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1
    conv => enter [1]; rw [l24 sK1]
    conv => enter [1, 2, 2]; rw [l7 sK1]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l29 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l26 sK1]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l30 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l27 sK1]
    conv => enter [1]; rw [← l22 sK1 (sK1 ◇ sK1)]
  have l31 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l29 sK1]
  have l33 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l30 sK1]
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ sK1)]
  have l34 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l33 sK1]
    conv => enter [1, 2]; rw [l7 sK1]
  have l35 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l34 sK1]
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l35 sK1]
    conv => enter [1]; rw [← l21 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l31 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [← l32 sK1]
  have l39 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l38 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l40 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l36 sK1]
    conv => enter [1]; rw [l21 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l36 sK1]
  have l41 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l21 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l42 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l41 sK1]
    conv => enter [1]; rw [← l39 sK1]
  have l43 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l40 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l44 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41595 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l45 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l44 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0]
    conv => enter [1]; rw [← l45 sK0]
  have l47 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1, 2]; rw [← l46 sK0]
  have l48 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41595 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l46 sK0]
  have l49 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l48 X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l50 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l47 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l51 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l49 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l31 sK0]
  have l52 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41595 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l43 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← h41595 X0 (sK1 ◇ sK1)]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0]
    conv => enter [1]; rw [l52 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l50 sK0]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1, 2]; rw [← l53 sK0 sK1]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [← l50 sK0]
  intro x y
  conv => enter [1]; rw [l55 x y]
  conv => enter [1]; rw [l42 y]

theorem Equation316_4512_implies_Equation41596 (G : Type*) [Magma G] (h316 : Equation316 G) (h4512 : Equation4512 G) : Equation41596 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h316 sK0 sK0]
  have l2 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l3 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l2 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1, 1]; rw [l0 X0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h316 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l7 : ∀ sK0 X2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l2 X2 sK0]
    conv => enter [1]; rw [l4 X2 X2 sK0]
  have l8 : ∀ X0 X2 sK0 X1 : G, ((X0 ◇ X0) ◇ X2) = ((sK0 ◇ sK0) ◇ (X1 ◇ X2)) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X2) sK0]
  have l9 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X2)]
    conv => enter [1]; rw [← l8 X0 X2 sK0 sK0]
  have l10 : ∀ sK0 X0 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l9 sK0 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

end Semigroup5
