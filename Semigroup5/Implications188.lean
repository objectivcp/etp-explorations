import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54502_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54502 : Equation54502 G) : Equation4278 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54502 (sK0 ◇ sK0) X0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54502 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X3 ◇ X2)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54502 X0 X1 X2]
    conv => enter [1]; rw [← h54502 X0 X3 X2]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54502 X0 X1 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54502 sK0 X0 sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l11 sK0 X0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l12 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l15 sK0]
    conv => enter [1]; rw [l10 sK0 sK2]
  have l17 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l10 sK0 sK2]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ sK0)]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l16 sK0 sK2]
    conv => enter [1]; rw [l18 sK0 sK2]
  have l20 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) ◇ X0) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l16 sK0 sK2]
  have l21 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l20 sK0 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ sK0) X0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l13 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK2]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l26 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l27 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l13 sK0 sK2]
    conv => enter [1]; rw [l26 sK0 sK2]
  have l28 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l24 sK0 sK2]
    conv => enter [1]; rw [l27 sK0 sK2]
  have l29 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l28 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ sK0) X0]
  have l30 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l13 sK0 sK2]
  have l31 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54502 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l13 sK0 sK2]
  have l32 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l31 sK0 X0 sK2]
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ sK0)]
  have l34 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l32 sK0 X0 sK2]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ (sK2 ◇ sK0)) sK2]
  have l35 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [← l25 sK0 (sK2 ◇ sK0)]
  have l36 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l34 sK0 X0 sK2]
    conv => enter [1]; rw [← l4 sK0 (sK2 ◇ sK0)]
  have l37 : ∀ sK0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l35 sK0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l38 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l36 sK0 X0 sK2]
    conv => enter [1]; rw [← l25 sK0 (sK2 ◇ sK0)]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l37 sK0 sK0]
  have l40 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l38 sK0 X0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l39 sK0]
    conv => enter [1]; rw [← l25 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l40 sK0 X0 sK0]
  have l43 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l42 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l44 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l43 sK0 X0]
    conv => enter [1]; rw [l10 sK0 sK2]
  have l45 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l44 sK0 X0 sK0]
  have l46 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l45 sK0 X0]
    conv => enter [1]; rw [← h54502 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l47 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← l46 sK0 X0 X1]
    conv => enter [1]; rw [l16 sK0 sK2]
  have l48 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l47 X0 X1 sK0 sK0]
  have l49 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l48 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l41 sK0]
  have l50 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 X0 (sK0 ◇ sK0) sK0 X1]
  have l51 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l7 X0 sK2 sK0 X0]
    conv => enter [1]; rw [← l50 X0 sK0 X0]
  have l52 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l49 sK0 X0]
    conv => enter [1]; rw [← l51 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l52 x y z]

theorem Equation4278_4512_implies_Equation54514 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54514 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4278 sK1 sK3 sK0]
  have l2 : ∀ X0 X1 sK0 sK1 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK3]
  have l3 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1 sK3]
  have l4 : ∀ sK3 sK0 sK1 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 X1]
  have l5 : ∀ X0 sK3 sK0 sK1 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK3 sK0 sK1 X1
    conv => enter [1]; rw [l3 X0 sK3 sK0 sK1]
    conv => enter [1]; rw [← l3 X1 sK3 sK0 sK1]
  have l6 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK1 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK1 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK1 sK1 sK2]
  have l7 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l8 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l7 sK1 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK1 sK3]
  have l9 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l8 sK1 X0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK1 sK1 sK1 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l9 sK1 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l11 z w x y]

theorem Equation4512_54514_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54514 : Equation54514 G) : Equation4278 G := by
  have l0 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [h54514 X1 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54514 X1 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l2 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK2 sK0 sK0]
  have l3 : ∀ X1 sK2 sK0 X0 : G, (X1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK2 sK0 X0
    conv => enter [1]; rw [l0 X1 sK2 sK0 X1]
    conv => enter [1]; rw [← l1 X0 sK0 X1]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l3 sK1 sK2 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l4 y z x x]

theorem Equation4278_4512_implies_Equation54416 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54416 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK2 sK0]
    conv => enter [1]; rw [h4278 sK1 X0 sK0]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK2 sK0]
    conv => enter [1]; rw [h4278 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 sK2 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h4278 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [h4278 sK1 sK2 sK0]
  have l3 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [← l2 sK1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [← h4278 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l3 X0 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK2 sK0 sK1 sK1]
  have l5 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l4 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l4 X1 sK2 sK0 sK1]
  have l6 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 2]; rw [← l1 X0 sK0 sK1 sK0]
    conv => enter [1]; rw [l5 X0 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK1 sK0]
  have l7 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l8 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l7 sK1 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK1 sK2]
  have l9 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l8 sK1 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK1 sK0 sK0]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← l11 y z x]

theorem Equation4512_54416_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54416 : Equation54416 G) : Equation4278 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54416 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK0 sK2 sK2]
    conv => enter [1]; rw [← h54416 X0 sK2 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54416 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 X0 sK2]
  have l4 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h54416 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 sK2]
  have l5 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l4 sK0 X0 sK2]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l2 sK0 X0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l6 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l9 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l6 X0 sK0 sK0]
  have l11 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l10 sK0 sK0 X1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4278_4512_implies_Equation54633 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54633 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4278 sK2 sK1 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 sK2]
  have l1 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK2) sK2 sK1]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [l1 X0 X0 sK2 sK1]
  have l3 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [h4278 sK2 sK3 sK0]
  have l5 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l2 X0 sK1 sK2]
    conv => enter [1]; rw [← l2 X1 sK1 sK2]
  have l6 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l7 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l6 sK2 X0 sK2 sK2]
    conv => enter [1, 2]; rw [l3 sK2 sK2 sK1 sK2]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l7 sK2 sK1 sK1]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l4 w z x y]
  conv => enter [1]; rw [l9 w z]

@[equational_result]
theorem Equation54633_implies_Equation4278 (G : Type*) [Magma G] (h54633 : Equation54633 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54633 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54633 X2 sK0 sK0 X0]
  have l1 : ∀ X2 sK0 X0 sK2 : G, (X2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X2 sK0 X0 sK2
    conv => enter [1]; rw [h54633 X2 sK0 sK0 X2]
    conv => enter [1]; rw [← h54633 X0 sK2 sK0 X2]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54623 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54623 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK0]
  have l2 : ∀ X0 X1 sK0 sK3 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK0 sK3 sK2
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK2]
  have l3 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK3 sK2]
  have l4 : ∀ sK2 sK0 sK3 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK2 sK0 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3 X1
    conv => enter [1]; rw [l3 X0 sK2 sK0 sK3]
    conv => enter [1]; rw [← l3 X1 sK2 sK0 sK3]
  have l6 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK3 sK2 X0]
    conv => enter [1]; rw [l5 X0 sK2 X0 sK3 X1]
    conv => enter [1, 2]; rw [l4 sK2 X0 sK3 sK1 sK2]
  have l7 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l8 : ∀ sK3 X0 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK2 sK0
    conv => enter [1]; rw [l7 sK3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 sK2]
  have l9 : ∀ sK3 X0 sK1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK1 sK2
    conv => enter [1]; rw [l8 sK3 X0 sK2 sK3]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK3 sK1 sK2]
  have l10 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l9 sK3 sK1 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [l4 sK3 sK3 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l11 w x z y]

theorem Equation4512_54623_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54623 : Equation54623 G) : Equation4278 G := by
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
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← h54623 (sK0 ◇ sK0) X1 X0 sK0]
  have l8 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54623 X0 X1 X2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X2)]
  have l9 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X2))) = (sK0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X0 ◇ X2))]
    conv => enter [1, 2]; rw [← h54623 X0 X1 X2 sK0]
  have l10 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l9 sK0 X0 X2 X1]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ X2)]
  have l11 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [← h54623 sK2 X0 sK0 X0]
    conv => enter [1]; rw [l8 sK2 X0 sK0 sK0]
  have l12 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l10 sK0 X0 X1 X2]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK0 ◇ sK0)) X0 X2 sK0]
  have l13 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l7 sK0 sK0 sK2]
    conv => enter [1]; rw [← l11 X0 sK2 sK0]
  have l14 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l12 sK0 X0 X1 X2]
    conv => enter [1]; rw [← l7 sK0 X2 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [l13 sK0 X0 sK2]
  have l16 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 X0 sK2]
  have l17 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l16 sK0 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK2 ◇ sK0))]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [l3 sK0 (sK2 ◇ sK0)]
  have l19 : ∀ sK0 X0 X1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 X1 sK2
    conv => enter [1]; rw [l17 sK0 X0 X1 sK2]
    conv => enter [1, 2]; rw [l8 X1 (X0 ◇ X1) (sK2 ◇ sK0) sK0]
  have l20 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l19 sK0 X0 sK0 sK2]
    conv => enter [1, 2]; rw [← l7 sK0 (sK2 ◇ sK0) sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54623 sK0 (sK0 ◇ sK0) sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h54623 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54623 sK0 sK0 sK0 X0]
  have l26 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [← h54623 sK0 X1 sK0 X0]
    conv => enter [1]; rw [← h54623 X1 X2 sK0 sK0]
  have l27 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← l14 sK0 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 sK0 X1 X2]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l24 sK0 X0]
  have l30 : ∀ sK0 X1 X2 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l27 sK0 X1 X2]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l29 sK0 sK0]
  have l32 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l30 sK0 X1 X2]
  have l33 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l32 sK0 X1 X2]
  have l34 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ sK0)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l33 sK0 X1 X2]
  have l35 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [l34 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l35 x y z]

theorem Equation4278_4512_implies_Equation54420 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54420 G := by
  have l0 : ∀ X0 sK1 sK2 sK3 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK1 sK2 sK3 X1
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK3) X0 sK1]
    conv => enter [1]; rw [h4278 (sK2 ◇ sK3) X1 sK1]
  have l1 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK3) sK1 sK1]
  have l2 : ∀ sK1 sK2 sK3 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK3]
    conv => enter [1]; rw [h4278 (sK2 ◇ sK3) X0 X1]
  have l3 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l4 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 sK3 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK3 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK1 sK3 X0 X1
    conv => enter [1]; rw [l4 sK0 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l6 : ∀ sK0 sK1 sK3 X0 X1 sK2 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK1 sK3 X0 X1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK3 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK3)]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK0 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l6 sK0 sK1 sK3 sK1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l7 y w z x]

theorem Equation4512_54420_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54420 : Equation54420 G) : Equation4278 G := by
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
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← h54420 X1 sK0 X0 (sK0 ◇ sK0)]
  have l7 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54420 X1 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54420 X1 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X0]
    conv => enter [1]; rw [← l7 X1 sK0 X0]
  have l10 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l9 sK2 sK0 X0]
  have l11 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l10 sK2 sK0 sK2]
    conv => enter [1]; rw [l7 sK2 sK0 X1]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l8 X0 sK0 X0]
    conv => enter [1]; rw [← l8 X1 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l8 X0 sK0 sK0]
  have l14 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1, 2]; rw [l8 X0 sK0 sK2]
    conv => enter [1]; rw [← l5 sK2 sK0 (sK2 ◇ sK0)]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 2]; rw [l8 X0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ sK0)]
  have l16 : ∀ sK2 X0 sK0 : G, (sK2 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [l14 sK2 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK2 ◇ sK0) (sK2 ◇ sK0)]
  have l17 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 (X0 ◇ X1) sK0 X2]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l12 (sK0 ◇ sK0) sK0 X0]
  have l19 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l11 sK2 sK0 sK2]
    conv => enter [1]; rw [← l18 sK0 sK2]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l17 X0 X1 sK0 sK0]
  have l21 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l19 sK2 sK0]
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0]
  have l23 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l21 sK2 sK0]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l23 sK0 sK2]
  have l25 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l22 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK2]
  have l26 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l27 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h54420 X0 sK2 sK0 sK0]
    conv => enter [1]; rw [l16 sK2 sK2 sK0]
  have l28 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l27 X0 sK2 sK0]
    conv => enter [1]; rw [← l26 sK0 (sK2 ◇ sK0) sK0]
  have l29 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l25 sK0 sK2]
    conv => enter [1]; rw [← l28 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l29 x y z]

theorem Equation4278_4512_implies_Equation54643 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54643 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK1 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK1]
  have l3 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4 sK1]
  have l4 : ∀ sK1 sK0 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK1 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ X0 sK1 sK0 sK4 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 X1
    conv => enter [1]; rw [l3 X0 sK1 sK0 sK4]
    conv => enter [1]; rw [← l3 X1 sK1 sK0 sK4]
  have l6 : ∀ X0 sK2 sK3 sK4 X1 : G, (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (X1 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK2 sK3 sK4 X1
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK4 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK4 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK4 sK2 sK3]
  have l7 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l8 : ∀ sK4 X0 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK1 sK0
    conv => enter [1]; rw [l7 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK1]
  have l9 : ∀ sK4 X0 sK2 sK3 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK4))) := by
    intro sK4 X0 sK2 sK3
    conv => enter [1]; rw [l8 sK4 X0 sK4 sK4]
    conv => enter [1, 2]; rw [l4 sK4 sK4 sK4 sK2 sK3]
  have l10 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← l9 sK4 sK2 sK2 sK3]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ sK4))) = (sK1 ◇ (sK0 ◇ sK4)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK4]
    conv => enter [1]; rw [l4 sK4 sK4 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l11 w u z x y]

theorem Equation4512_54643_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54643 : Equation54643 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54643 sK0 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54643 X0 X1 sK0 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54476 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54476 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK2]
  have l2 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [← h4278 sK0 (sK2 ◇ sK0) sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  have l4 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l2 X0 X1 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1]
  have l5 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l4 X0 X1 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l6 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l1 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [l5 X0 X0 sK2 sK0 sK1]
  have l7 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 X0 sK1 sK0 sK2]
  have l8 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [l7 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 X1 sK1 sK2 sK0]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4278 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0 sK1]
  have l12 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 sK0 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l15 x y z]

theorem Equation4512_54476_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54476 : Equation54476 G) : Equation4278 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54476 (sK0 ◇ sK0) X0 sK0]
  have l10 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X2 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← h54476 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54476 sK0 X0 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54476 X0 X1 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54476 X0 X1 sK0]
    conv => enter [1]; rw [← h54476 X0 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l12 sK0 X0 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l17 sK0 sK0]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l18 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [← l26 sK0 (sK0 ◇ sK0)]
  have l29 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54476 X0 sK0 sK0]
    conv => enter [1]; rw [h54476 sK0 X0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l29 X0 sK0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l30 sK0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l32 sK0 X0]
  have l34 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l15 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

theorem Equation4278_4512_implies_Equation54493 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54493 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK0) sK0 sK1]
  have l2 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1, 2]; rw [l0 sK1 sK0 X0]
    conv => enter [1]; rw [l1 X0 X0 sK0 sK1]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 sK1]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4278 sK0 sK2 sK1]
  have l5 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l2 X0 sK1 sK0]
    conv => enter [1]; rw [← l2 X1 sK1 sK0]
  have l6 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4278 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]
  conv => enter [1]; rw [l9 y z]

theorem Equation4512_54493_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54493 : Equation54493 G) : Equation4278 G := by
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
  have l3 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54493 X0 sK0 sK0]
  have l5 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54493 X0 X1 sK0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X2 ◇ (X3 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54493 (X2 ◇ X3) X1 X0]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X0)]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 sK0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l5 sK0 X1 X0]
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [← h54493 X0 sK2 sK0]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l10 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l12 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0 sK2]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0]
  have l15 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l16 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h54493 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l12 sK0 sK1 sK2]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l16 sK0 X0 sK1 sK2]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h54493 (sK2 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l15 sK2 sK0 sK1]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK2 sK0]
    conv => enter [1]; rw [l17 sK0 X0 sK1 sK2]
  have l20 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0 sK2]
    conv => enter [1]; rw [← l20 sK0 sK2 sK1]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l23 y z x x]

theorem Equation4278_4512_implies_Equation54529 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54529 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4278 sK1 sK2 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK1]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK1) sK1 sK2]
  have l2 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l0 sK2 sK1 X0]
    conv => enter [1]; rw [l1 X0 X0 sK1 sK2]
  have l3 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 sK0]
  have l4 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [h4278 sK1 sK3 sK0]
  have l5 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [l2 X0 sK2 sK1]
    conv => enter [1]; rw [← l2 X1 sK2 sK1]
  have l6 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l6 sK1 X0 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK1 sK2 sK1]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l7 sK1 sK1 sK2]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l8 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l4 w z x y]
  conv => enter [1]; rw [l9 w z]

@[equational_result]
theorem Equation54529_implies_Equation4278 (G : Type*) [Magma G] (h54529 : Equation54529 G) : Equation4278 G := by
  have l0 : ∀ X0 sK0 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [h54529 X0 sK0 sK0 X0]
    conv => enter [1]; rw [← h54529 X2 sK0 sK0 X0]
  have l1 : ∀ X2 sK0 X0 sK2 : G, (X2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro X2 sK0 X0 sK2
    conv => enter [1]; rw [h54529 X2 sK0 sK0 X2]
    conv => enter [1]; rw [← h54529 X0 sK2 sK0 X2]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation4278_4512_implies_Equation54612 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54612 G := by
  have l0 : ∀ X0 sK0 sK2 X1 : G, (X0 ◇ (sK0 ◇ sK2)) = (X1 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2 X1
    conv => enter [1]; rw [← h4278 sK2 X0 sK0]
    conv => enter [1]; rw [h4278 sK2 X1 sK0]
  have l1 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [← h4278 sK2 sK3 sK0]
  have l2 : ∀ X0 X1 sK0 sK2 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 sK0 sK2 sK3
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK2) sK0 sK2 sK3]
  have l3 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK2 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK2 sK3]
  have l4 : ∀ sK3 sK0 sK2 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK2]
    conv => enter [1]; rw [h4278 sK2 X0 X1]
  have l5 : ∀ X0 sK3 sK0 sK2 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK3 sK0 sK2 X1
    conv => enter [1]; rw [l3 X0 sK3 sK0 sK2]
    conv => enter [1]; rw [← l3 X1 sK3 sK0 sK2]
  have l6 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1, 2]; rw [l4 sK2 sK1 sK2 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK2 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK2 sK2 sK1]
  have l7 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l8 : ∀ sK2 X0 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 sK3 sK0
    conv => enter [1]; rw [l7 sK2 X0 sK2 sK0]
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK2 sK3]
  have l9 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l8 sK2 X0 sK2 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK2 sK2 sK2 sK1]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK1 sK1]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK3 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK2 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l11 w z x y]

theorem Equation4512_54612_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54612 : Equation54612 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 X4 X5 : G, (X0 ◇ (X1 ◇ X2)) = (X4 ◇ (X5 ◇ X2)) := by
    intro X0 X1 X2 X4 X5
    conv => enter [1]; rw [h54612 X0 X1 X2 X0]
    conv => enter [1]; rw [← h54612 X4 X5 X2 X0]
  have l3 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h54612 X0 X1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54612 X0 X1 (sK0 ◇ sK0) sK0]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l4 sK0 X1 sK0]
    conv => enter [1]; rw [l4 sK0 X0 sK0]
  have l6 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l5 sK2 sK0 X0]
  have l7 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK2]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 sK0 sK0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l11 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [l2 X0 X1 sK0 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l1 sK0 X2]
  have l13 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l11 X0 X1 sK0 sK0]
  have l14 : ∀ sK0 X2 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X2 sK2
    conv => enter [1]; rw [← l12 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK0 X2 sK2]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0 sK0 sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation4278_4512_implies_Equation54560 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54560 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK0]
  have l2 : ∀ X0 X1 sK0 sK3 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK0 sK3 sK2
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK3) sK0 sK3 sK2]
  have l3 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = ((sK0 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1, 2]; rw [l0 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK3 sK2]
  have l4 : ∀ sK2 sK0 sK3 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK2 sK0 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3 X1
    conv => enter [1]; rw [l3 X0 sK2 sK0 sK3]
    conv => enter [1]; rw [← l3 X1 sK2 sK0 sK3]
  have l6 : ∀ X0 sK2 sK1 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK2 sK1 sK3 X1
    conv => enter [1, 2]; rw [l4 sK2 sK1 sK3 sK2 X0]
    conv => enter [1]; rw [l5 X0 sK2 X0 sK3 X1]
    conv => enter [1, 2]; rw [l4 sK2 X0 sK3 sK2 sK1]
  have l7 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l8 : ∀ sK3 X0 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK2 sK0
    conv => enter [1]; rw [l7 sK3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 sK2]
  have l9 : ∀ sK3 X0 sK2 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 sK2 sK1
    conv => enter [1]; rw [l8 sK3 X0 sK2 sK3]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK3 sK2 sK1]
  have l10 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l9 sK3 sK1 sK2 sK1]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK3]
    conv => enter [1]; rw [l4 sK3 sK3 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l11 w x z y]

theorem Equation4512_54560_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54560 : Equation54560 G) : Equation4278 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54560 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l4 sK0 sK0 X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l4 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54560 X0 sK2 sK0 sK0]
  have l9 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 X0 sK2]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4278_4512_implies_Equation54586 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54586 G := by
  have l0 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l1 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK1]
  have l2 : ∀ X0 X1 sK1 sK3 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 X1 sK1 sK3 sK2
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ sK3) sK1 sK3 sK2]
  have l3 : ∀ X0 sK2 sK1 sK3 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = ((sK1 ◇ sK3) ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK2 sK1 sK3
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK3 X0]
    conv => enter [1]; rw [l2 X0 X0 sK1 sK3 sK2]
  have l4 : ∀ sK2 sK1 sK3 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK1 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK2 sK1 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK2 sK1 sK3 X1
    conv => enter [1]; rw [l3 X0 sK2 sK1 sK3]
    conv => enter [1]; rw [← l3 X1 sK2 sK1 sK3]
  have l6 : ∀ sK3 X0 X1 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 X1 sK2
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ sK3)]
  have l7 : ∀ sK3 X0 sK2 sK1 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK3 X0 sK2 sK1
    conv => enter [1]; rw [l6 sK3 X0 sK3 sK2]
    conv => enter [1, 2]; rw [l4 sK3 sK2 sK3 sK2 sK1]
  have l8 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l7 sK3 sK1 sK2 sK1]
  have l9 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ sK3)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [l4 sK2 sK1 sK3 sK3 sK3]
    conv => enter [1]; rw [← l8 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z y w]
  conv => enter [1]; rw [l9 y w z]

theorem Equation4512_54586_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54586 : Equation54586 G) : Equation4278 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54586 X0 sK0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l6 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l5 X0 sK0 X1]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l7 : ∀ sK0 X0 X2 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X2 X1
    conv => enter [1, 2]; rw [← l6 X1 sK0 X0]
    conv => enter [1]; rw [← h54586 X2 X1 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1]; rw [← l4 sK0 X0]
  have l10 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [l7 sK0 X0 X2 X1]
  have l11 : ∀ sK0 X0 X2 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X2 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X2 X1
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l10 sK0 X0 X2 X1]
  have l12 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4278_4512_implies_Equation54667 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54667 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK1 sK0]
  have l2 : ∀ X0 X1 sK0 sK4 sK1 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK0 sK4 sK1
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK4) sK0 sK4 sK1]
  have l3 : ∀ X0 sK1 sK0 sK4 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = ((sK0 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK4 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK4 sK1]
  have l4 : ∀ sK1 sK0 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK1 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l5 : ∀ X0 sK1 sK0 sK4 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 X1
    conv => enter [1]; rw [l3 X0 sK1 sK0 sK4]
    conv => enter [1]; rw [← l3 X1 sK1 sK0 sK4]
  have l6 : ∀ X0 sK3 sK2 sK4 X1 : G, (X0 ◇ (sK3 ◇ (sK2 ◇ sK4))) = (X1 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro X0 sK3 sK2 sK4 X1
    conv => enter [1, 2]; rw [l4 sK3 sK2 sK4 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK4 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK4 sK3 sK2]
  have l7 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l8 : ∀ sK4 X0 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK1 sK0
    conv => enter [1]; rw [l7 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK1]
  have l9 : ∀ sK4 X0 sK3 sK2 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK2 ◇ sK4))) := by
    intro sK4 X0 sK3 sK2
    conv => enter [1]; rw [l8 sK4 X0 sK4 sK4]
    conv => enter [1, 2]; rw [l4 sK4 sK4 sK4 sK3 sK2]
  have l10 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← l9 sK4 sK2 sK3 sK2]
  have l11 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ sK4))) = (sK1 ◇ (sK0 ◇ sK4)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l10 sK2 sK3 sK4]
    conv => enter [1]; rw [l4 sK4 sK4 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l11 w u z x y]

theorem Equation4512_54667_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54667 : Equation54667 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54667 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X2)]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X2]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 sK0]
  have l5 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 sK2 sK0 sK0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4278_4512_implies_Equation54468 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54468 G := by
  have l0 : ∀ X0 sK1 sK2 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0 X1
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [h4278 (sK2 ◇ sK0) X1 sK1]
  have l1 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h4278 sK0 X0 sK1]
    conv => enter [1]; rw [h4278 sK0 X1 sK1]
  have l2 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ sK0)) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [← h4278 sK0 X0 sK1]
    conv => enter [1]; rw [h4278 sK0 X1 X2]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4278 sK0 sK1 sK1]
  have l4 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4278 sK0 X0 X1]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK0 X0]
  have l6 : ∀ X2 sK1 sK0 X3 X0 X1 : G, (X2 ◇ (sK1 ◇ sK0)) = (X3 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro X2 sK1 sK0 X3 X0 X1
    conv => enter [1]; rw [l2 X2 sK1 sK0 (X3 ◇ X0) X1]
    conv => enter [1]; rw [← h4512 X3 X0 (X1 ◇ sK0)]
  have l7 : ∀ X2 sK1 sK0 X3 : G, (X2 ◇ (sK1 ◇ sK0)) = (X3 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro X2 sK1 sK0 X3
    conv => enter [1]; rw [l6 X2 sK1 sK0 X3 X2 X2]
    conv => enter [1, 2]; rw [l4 X2 sK0 sK1 sK1]
  have l8 : ∀ X2 sK1 sK0 X3 sK2 : G, (X2 ◇ (sK1 ◇ sK0)) = (X3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro X2 sK1 sK0 X3 sK2
    conv => enter [1]; rw [l7 X2 sK1 sK0 X3]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 X2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X2
    conv => enter [1]; rw [l5 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l8 X2 sK1 sK0 sK0 sK0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK0 sK1 sK1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 sK1 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4512_54468_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54468 : Equation54468 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ X0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54468 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54468 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54468 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 sK0 X0]
    conv => enter [1]; rw [h54468 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← l3 sK0 X1 X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l2 sK0 X1 X0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 (X0 ◇ sK0) X0]
    conv => enter [1]; rw [← h54468 X0 X1 sK0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 sK0 X0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation4278_4512_implies_Equation54534 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54534 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h4278 sK1 X0 sK0]
    conv => enter [1]; rw [h4278 sK1 X1 sK0]
  have l1 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h4278 sK1 sK3 sK0]
  have l2 : ∀ X0 X1 sK0 sK1 sK3 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 (sK0 ◇ sK1) X0 X1]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0 sK1 sK3]
  have l3 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [l2 X0 X0 sK0 sK1 sK3]
  have l4 : ∀ sK3 sK0 sK1 X0 X1 : G, (sK3 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ sK1)) := by
    intro sK3 sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK1]
    conv => enter [1]; rw [h4278 sK1 X0 X1]
  have l5 : ∀ X0 sK3 sK0 sK1 X1 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK3 sK0 sK1 X1
    conv => enter [1]; rw [l3 X0 sK3 sK0 sK1]
    conv => enter [1]; rw [← l3 X1 sK3 sK0 sK1]
  have l6 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1, 2]; rw [l4 sK2 sK2 sK1 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK1 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK1 sK2 sK2]
  have l7 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l8 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l7 sK1 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK0 sK1 sK3]
  have l9 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l8 sK1 X0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK1 sK1 sK2 sK2]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l9 sK1 sK1 sK2]
  have l11 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK1 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [← l11 z w x y]

theorem Equation4512_54534_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54534 : Equation54534 G) : Equation4278 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54534 X0 X1 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4278_4512_implies_Equation54433 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54433 G := by
  have l0 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0 sK1 sK1]
  intro x y z
  conv => enter [1]; rw [← h4278 z x y]
  conv => enter [1]; rw [l1 z y]

theorem Equation4512_54433_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54433 : Equation54433 G) : Equation4278 G := by
  have l0 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54433 X1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54433 X0 sK0 sK0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54433 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ X1)]
  have l3 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [← h54433 X0 sK2 sK0]
  have l4 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 X0 sK2]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0 sK2]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 X0]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l6 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l8 y z x x]

theorem Equation4278_4512_implies_Equation54607 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54607 G := by
  have l0 : ∀ X0 X1 sK2 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK2) X0 X1]
    conv => enter [1, 2]; rw [← h4278 sK2 (sK2 ◇ sK2) sK2]
  have l1 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1, 2]; rw [h4278 sK2 X0 sK2]
    conv => enter [1]; rw [l0 X0 X0 sK2]
  have l2 : ∀ sK2 X0 X1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK2 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l3 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 X0 sK2 sK2]
  have l4 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← h4278 z x y]
  conv => enter [1]; rw [l4 z w]

theorem Equation4512_54607_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54607 : Equation54607 G) : Equation4278 G := by
  have l0 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54607 X0 X1 sK0 sK2]
  have l1 : ∀ X0 sK0 X1 sK2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK0 X1 sK2
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54607 X1 sK2 sK0 X0]
  have l2 : ∀ sK2 sK0 X1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 X1
    conv => enter [1]; rw [l0 sK2 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK2 sK0 X1 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54607 sK0 sK0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [l2 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4278_4512_implies_Equation54545 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54545 G := by
  have l0 : ∀ X0 sK0 sK3 X1 : G, (X0 ◇ (sK0 ◇ sK3)) = (X1 ◇ (sK0 ◇ sK3)) := by
    intro X0 sK0 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK0]
    conv => enter [1]; rw [h4278 sK3 X1 sK0]
  have l1 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h4278 sK3 sK2 sK0]
  have l2 : ∀ sK2 sK0 sK3 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK2 sK0 sK3 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l3 : ∀ X0 X1 sK2 sK3 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro X0 X1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4278 (sK2 ◇ sK3) X0 X1]
    conv => enter [1, 2]; rw [l2 (sK2 ◇ sK3) sK2 sK3 sK2 sK0]
  have l4 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l3 X0 X1 sK2 sK3 X0]
    conv => enter [1, 2]; rw [l2 sK2 X0 sK3 sK2 sK2]
  have l5 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK3 X0 sK2]
    conv => enter [1]; rw [l4 X0 X0 sK2 sK3]
  have l6 : ∀ X0 sK2 sK3 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3
    conv => enter [1, 2]; rw [l2 sK2 sK2 sK3 sK2 X0]
    conv => enter [1]; rw [l5 X0 sK2 X0 sK3]
  have l7 : ∀ sK1 sK2 sK3 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK3]
    conv => enter [1]; rw [← l6 X0 sK2 sK3]
  have l8 : ∀ sK3 X0 X1 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK3 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK3)]
  have l9 : ∀ sK3 X0 sK2 sK0 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) := by
    intro sK3 X0 sK2 sK0
    conv => enter [1]; rw [l8 sK3 X0 sK3 sK0]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK3 sK2]
  have l10 : ∀ sK3 X0 sK2 : G, (sK3 ◇ (sK3 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK3 X0 sK2
    conv => enter [1]; rw [l9 sK3 X0 sK2 sK3]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK3 sK2 sK2]
  have l11 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l10 sK3 sK1 sK2]
  have l12 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (sK2 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK3]
    conv => enter [1]; rw [l2 sK3 sK3 sK3 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [← l12 w x z y]

theorem Equation4512_54545_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54545 : Equation54545 G) : Equation4278 G := by
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
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l6 : ∀ X1 sK0 X0 X2 : G, (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro X1 sK0 X0 X2
    conv => enter [1, 2]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [← h54545 (sK0 ◇ sK0) X2 X0 X1]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h54545 sK0 sK0 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X1 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 X0]
    conv => enter [1]; rw [h54545 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54545 sK0 X0 X1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X1)]
  have l10 : ∀ sK2 sK0 X2 X1 X0 : G, ((sK2 ◇ sK0) ◇ (X2 ◇ X1)) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ X1)))) := by
    intro sK2 sK0 X2 X1 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (X2 ◇ X1)]
    conv => enter [1, 2]; rw [h54545 sK0 X2 X1 X0]
  have l11 : ∀ sK0 X2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)))) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X2 ◇ X1)]
    conv => enter [1, 2]; rw [h54545 (sK0 ◇ sK0) X2 X1 X0]
  have l12 : ∀ sK0 X2 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)))) := by
    intro sK0 X2 X1 X0
    conv => enter [1]; rw [l11 sK0 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 X1]
  have l13 : ∀ sK2 sK0 X2 X1 X0 : G, ((sK2 ◇ sK0) ◇ (X2 ◇ X1)) = (sK2 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK2 sK0 X2 X1 X0
    conv => enter [1]; rw [l10 sK2 sK0 X2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X1]
  have l14 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1]
  have l15 : ∀ sK0 X0 X2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 X0 X2]
  have l16 : ∀ sK0 X2 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X1)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l12 sK0 X2 X1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 X1 sK0]
  have l17 : ∀ sK2 sK0 X2 X1 : G, ((sK2 ◇ sK0) ◇ (X2 ◇ X1)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK2 sK0 X2 X1
    conv => enter [1]; rw [l13 sK2 sK0 X2 X1 sK2]
    conv => enter [1, 2]; rw [← l7 sK0 X1 sK2]
  have l18 : ∀ sK0 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X2 ◇ X0)) := by
    intro sK0 X0 X2
    conv => enter [1]; rw [← l14 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l15 sK0 X0 X2]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l14 sK0 sK0 sK0]
    conv => enter [1]; rw [h54545 sK0 sK0 sK0 X0]
  have l20 : ∀ sK0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X1)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)]
    conv => enter [1]; rw [← l16 sK0 X2 X1]
  have l21 : ∀ sK0 X1 sK2 X2 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK2 ◇ sK0) ◇ (X2 ◇ X1)) := by
    intro sK0 X1 sK2 X2
    conv => enter [1]; rw [l7 sK0 X1 sK2]
    conv => enter [1]; rw [← l17 sK2 sK0 X2 X1]
  have l22 : ∀ sK0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ X1)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l18 sK0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X1 X2]
  have l23 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l19 sK0 X1]
    conv => enter [1]; rw [l19 sK0 X0]
  have l24 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l5 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l19 sK0 X0]
  have l25 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l25 sK0 X0 X1]
  have l27 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l21 sK0 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l24 sK2 sK0 X0]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 sK0 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l28 sK0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l23 sK0 sK0 X0]
  have l31 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l30 sK0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1, 1]; rw [l31 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK0 ◇ sK0) X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l32 sK0 X0 sK0]
  have l34 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ X1)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l14 sK0 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h54545 X0 X2 X1 sK0]
  have l35 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ (X2 ◇ X1)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l22 sK0 X1 X0]
    conv => enter [1]; rw [l34 sK0 X0 X1 X2]
  have l36 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X2 ◇ X1)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l33 sK0 X1]
    conv => enter [1]; rw [l35 sK0 X1 X0 X2]
  have l37 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l37 x y z]

theorem Equation4278_4512_implies_Equation54457 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54457 G := by
  have l0 : ∀ X0 sK0 sK1 sK3 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK3))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 (sK1 ◇ sK3) X0 sK0]
    conv => enter [1]; rw [h4278 (sK1 ◇ sK3) X1 sK0]
  have l1 : ∀ X0 sK1 sK3 X1 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (sK1 ◇ sK3)) := by
    intro X0 sK1 sK3 X1
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 sK1]
  have l2 : ∀ X0 sK1 sK3 X1 X2 : G, (X0 ◇ (sK1 ◇ sK3)) = (X1 ◇ (X2 ◇ sK3)) := by
    intro X0 sK1 sK3 X1 X2
    conv => enter [1]; rw [← h4278 sK3 X0 sK1]
    conv => enter [1]; rw [h4278 sK3 X1 X2]
  have l3 : ∀ sK0 sK1 sK3 : G, (sK0 ◇ (sK1 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro sK0 sK1 sK3
    conv => enter [1]; rw [← h4278 sK3 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK3 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK3)) = (X0 ◇ (X1 ◇ sK3)) := by
    intro sK0 sK1 sK3 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK3]
    conv => enter [1]; rw [h4278 sK3 X0 X1]
  have l5 : ∀ X0 sK2 sK3 X1 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK3 X1
    conv => enter [1, 2]; rw [l4 sK2 sK2 sK3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 sK3 X1]
    conv => enter [1, 2]; rw [l4 X0 X0 sK3 sK2 sK2]
  have l6 : ∀ X2 sK1 sK3 X3 X0 X1 : G, (X2 ◇ (sK1 ◇ sK3)) = (X3 ◇ (X0 ◇ (X1 ◇ sK3))) := by
    intro X2 sK1 sK3 X3 X0 X1
    conv => enter [1]; rw [l2 X2 sK1 sK3 (X3 ◇ X0) X1]
    conv => enter [1]; rw [← h4512 X3 X0 (X1 ◇ sK3)]
  have l7 : ∀ X2 sK1 sK3 X3 sK0 : G, (X2 ◇ (sK1 ◇ sK3)) = (X3 ◇ (sK0 ◇ (sK1 ◇ sK3))) := by
    intro X2 sK1 sK3 X3 sK0
    conv => enter [1]; rw [l6 X2 sK1 sK3 X3 X2 X2]
    conv => enter [1, 2]; rw [l4 X2 X2 sK3 sK0 sK1]
  have l8 : ∀ X2 sK1 sK3 X3 sK2 : G, (X2 ◇ (sK1 ◇ sK3)) = (X3 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X2 sK1 sK3 X3 sK2
    conv => enter [1]; rw [l7 X2 sK1 sK3 X3 X2]
    conv => enter [1, 2]; rw [l4 X2 sK1 sK3 sK2 sK2]
  have l9 : ∀ sK1 sK2 sK3 X2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X2 ◇ (sK1 ◇ sK3)) := by
    intro sK1 sK2 sK3 X2
    conv => enter [1]; rw [← l8 X2 sK1 sK3 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l9 y w z x]

theorem Equation4512_54457_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54457 : Equation54457 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h54457 X0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54457 sK0 sK0 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l3 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [← h54457 X0 sK2 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← h54457 X0 sK0 sK0 sK0]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54457 (X0 ◇ X1) sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4278_4512_implies_Equation54673 (G : Type*) [Magma G] (h4278 : Equation4278 G) (h4512 : Equation4512 G) : Equation54673 G := by
  have l0 : ∀ X0 sK0 sK4 X1 : G, (X0 ◇ (sK0 ◇ sK4)) = (X1 ◇ (sK0 ◇ sK4)) := by
    intro X0 sK0 sK4 X1
    conv => enter [1]; rw [← h4278 sK4 X0 sK0]
    conv => enter [1]; rw [h4278 sK4 X1 sK0]
  have l1 : ∀ sK1 sK0 sK4 : G, (sK1 ◇ (sK0 ◇ sK4)) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK1 sK0 sK4
    conv => enter [1]; rw [← h4278 sK4 sK1 sK0]
  have l2 : ∀ sK1 sK0 sK4 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK4)) = (X0 ◇ (X1 ◇ sK4)) := by
    intro sK1 sK0 sK4 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 sK4]
    conv => enter [1]; rw [h4278 sK4 X0 X1]
  have l3 : ∀ X0 X1 sK3 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro X0 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4278 (sK3 ◇ sK4) X0 X1]
    conv => enter [1, 2]; rw [l2 (sK3 ◇ sK4) sK3 sK4 sK1 sK0]
  have l4 : ∀ X0 X1 sK3 sK4 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro X0 X1 sK3 sK4
    conv => enter [1]; rw [l3 X0 X1 sK3 sK4 X0 X0]
    conv => enter [1, 2]; rw [l2 X0 X0 sK4 sK3 sK3]
  have l5 : ∀ X0 sK1 sK0 sK4 sK3 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK1 sK0 sK4 sK3
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK4 X0 sK3]
    conv => enter [1]; rw [l4 X0 X0 sK3 sK4]
  have l6 : ∀ X0 sK3 sK4 : G, (X0 ◇ (sK3 ◇ (sK3 ◇ sK4))) = ((sK3 ◇ sK4) ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro X0 sK3 sK4
    conv => enter [1, 2]; rw [l2 sK3 sK3 sK4 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 sK4 sK3]
  have l7 : ∀ sK2 sK3 sK4 X0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro sK2 sK3 sK4 X0
    conv => enter [1]; rw [l6 sK2 sK3 sK4]
    conv => enter [1]; rw [← l6 X0 sK3 sK4]
  have l8 : ∀ sK4 X0 X1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 X1 sK0
    conv => enter [1]; rw [h4278 sK4 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK4)]
  have l9 : ∀ sK4 X0 sK1 sK0 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK4))) := by
    intro sK4 X0 sK1 sK0
    conv => enter [1]; rw [l8 sK4 X0 sK4 sK0]
    conv => enter [1, 2]; rw [l0 sK4 sK0 sK4 sK1]
  have l10 : ∀ sK4 X0 sK3 : G, (sK4 ◇ (sK4 ◇ sK4)) = (X0 ◇ (sK3 ◇ (sK3 ◇ sK4))) := by
    intro sK4 X0 sK3
    conv => enter [1]; rw [l9 sK4 X0 sK4 sK4]
    conv => enter [1, 2]; rw [l2 sK4 sK4 sK4 sK3 sK3]
  have l11 : ∀ sK2 sK3 sK4 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) = (sK4 ◇ (sK4 ◇ sK4)) := by
    intro sK2 sK3 sK4
    conv => enter [1]; rw [← l10 sK4 sK2 sK3]
  have l12 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK3 ◇ (sK3 ◇ sK4))) = (sK1 ◇ (sK0 ◇ sK4)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l11 sK2 sK3 sK4]
    conv => enter [1]; rw [l2 sK4 sK4 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [← l12 w u z x y]

theorem Equation4512_54673_implies_Equation4278 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54673 : Equation54673 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h54673 X0 X1 X2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X2)]
  have l3 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l2 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l1 sK0 X2]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 sK0 X0 sK0]
  have l5 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l3 X0 sK2 sK0 sK0]
  have l6 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation4279_implies_Equation4324 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4324 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

@[equational_result]
theorem Equation4324_implies_Equation4279 (G : Type*) [Magma G] (h4324 : Equation4324 G) : Equation4279 G := by
  have l0 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h4324 X0 X1 sK1]
    conv => enter [1]; rw [h4324 X1 sK1 sK2]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4324 X0 X1 sK0]
    conv => enter [1]; rw [h4324 X1 sK0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

@[equational_result]
theorem Equation4279_implies_Equation4336 (G : Type*) [Magma G] (h4279 : Equation4279 G) : Equation4336 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4279 sK1 sK1 sK2]
    conv => enter [1]; rw [h4279 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation4336_implies_Equation4279 (G : Type*) [Magma G] (h4336 : Equation4336 G) : Equation4279 G := by
  have l0 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4336 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [h4336 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y z x]

theorem Equation4279_4512_implies_Equation54052 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54052 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK2) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK1 X0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_54052_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54052 : Equation54052 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54052 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54052 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ X0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ X0) X1]
  have l5 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l4 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l6 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ X1)]
    conv => enter [1]; rw [← l5 sK1 sK2 X1 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))]
    conv => enter [1]; rw [← h54052 X0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4279_4512_implies_Equation54054 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54054 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y y x z]

theorem Equation4512_54054_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54054 : Equation54054 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54054 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54054 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ sK2)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54054 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l9 sK0 X0]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l10 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54054 X0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0 X0]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
    conv => enter [1]; rw [← h54054 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l18 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK0 sK2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1, 2]; rw [← l16 sK0 X0]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l18 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation4279_4512_implies_Equation54068 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54068 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y y z x]

theorem Equation4512_54068_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54068 : Equation54068 G) : Equation4279 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54068 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h54068 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h54068 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l3 sK0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54068 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54068 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1, 2]; rw [← h54068 sK0 sK0 X0]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK0 X1 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l9 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 (sK0 ◇ sK0) sK0 sK0 X0]
    conv => enter [1]; rw [← l12 X0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54068 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l16 sK0 X0]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← l17 X0 sK0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0 X0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54068 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l21 sK0 (X0 ◇ X1)]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK0]
    conv => enter [1]; rw [← l16 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l23 y z x]

theorem Equation4279_4512_implies_Equation54069 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54069 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK2 sK0]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X0 ◇ X1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l1 X1 X0 sK0 sK1]
  have l3 : ∀ sK0 sK1 X1 X2 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [l1 sK0 sK1 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l4 : ∀ sK0 sK1 X1 X2 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [l3 sK0 sK1 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l4 sK0 sK1 X1 X2 sK0]
    conv => enter [1, 2, 2]; rw [h4279 sK0 (sK0 ◇ sK2) sK2]
  have l7 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l6 sK0 sK1 X1 X2 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l7 sK0 sK1 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_54069_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54069 : Equation54069 G) : Equation4279 G := by
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
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54069 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [l1 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54069 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ (sK2 ◇ sK1))) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h54069 (sK2 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l7 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK2 ◇ sK1) ◇ sK2)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54069 sK1 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = (X2 ◇ ((X2 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h54069 (X2 ◇ X0) X0 X1]
    conv => enter [1]; rw [← h54069 X2 (X2 ◇ X0) X0]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54069 (X2 ◇ X3) X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X2 ◇ X3))]
  have l10 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← h54069 X0 X1 X2]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h54069 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (X0 ◇ X1))]
  have l12 : ∀ sK2 X0 sK1 X1 : G, (sK2 ◇ (X0 ◇ (sK1 ◇ X0))) = ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 sK1 X1
    conv => enter [1, 2]; rw [h54069 X0 sK1 X1]
    conv => enter [1]; rw [h4512 sK2 sK1 (X1 ◇ (X0 ◇ X1))]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54069 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h54069 sK1 sK2 X0]
    conv => enter [1]; rw [l12 sK2 X0 sK1 X1]
  have l15 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h54069 sK0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 X1]
  have l16 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l10 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l17 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X2 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l9 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X1 X0]
  have l22 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l16 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X2 X0 X1]
    conv => enter [1]; rw [l18 X0 X1 X2]
  have l24 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l20 sK0 X1 X0]
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 X1 X0]
  have l26 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l22 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ X2) X3]
  have l27 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l24 sK0 X1 X0]
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l28 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l26 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l29 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l27 sK0 X1 X0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 X1 X0]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l30 sK0 sK0 sK0]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l33 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l35 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l37 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1 sK2]
    conv => enter [1]; rw [h54069 sK2 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l38 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ (X1 ◇ sK2)) = (X1 ◇ ((X0 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [h54069 sK2 X1 (X0 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [h54069 sK2 X0 sK1]
  have l39 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((X0 ◇ sK2) ◇ X1)) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK2 (X0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [h54069 sK2 X0 sK1]
  have l40 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((X0 ◇ sK2) ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [l39 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) X1]
  have l41 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ (X1 ◇ sK2)) = (X1 ◇ (X0 ◇ (sK2 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [l38 sK2 X1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l42 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1]; rw [l37 sK2 sK1]
  have l43 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [← l40 sK2 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l44 : ∀ sK2 X1 sK1 : G, (sK2 ◇ (X1 ◇ sK2)) = (sK2 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 X1 sK1
    conv => enter [1]; rw [l41 sK2 X1 sK2 sK1]
    conv => enter [1]; rw [← l28 sK2 X1 (sK1 ◇ (sK2 ◇ sK1)) sK2]
  have l45 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l42 sK1 sK2]
  have l46 : ∀ sK2 X1 sK1 : G, (sK2 ◇ (X1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 X1 sK1
    conv => enter [1]; rw [l44 sK2 X1 sK1]
    conv => enter [1]; rw [← l43 X1 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l47 : ∀ sK2 X1 sK1 : G, (sK2 ◇ (X1 ◇ sK2)) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK2 X1 sK1
    conv => enter [1]; rw [l46 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← l45 sK1 sK2]
  have l48 : ∀ X1 sK1 sK2 : G, (X1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [← h54069 sK2 X1 sK1]
    conv => enter [1]; rw [l47 sK2 X1 sK1]
  have l49 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54069 X0 X1 sK0]
    conv => enter [1, 2]; rw [l19 sK0 X0]
  have l50 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK0 X0]
    conv => enter [1, 2]; rw [l19 sK0 X0]
  have l51 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l14 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l52 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK2 sK2 X0]
    conv => enter [1, 2]; rw [h54069 sK2 X0 sK1]
  have l53 : ∀ sK2 sK1 X0 X1 X2 : G, ((sK2 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) := by
    intro sK2 sK1 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← l14 sK1 sK2 X0 X1]
  have l54 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [← l53 sK2 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l55 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l56 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 sK1]
  have l57 : ∀ sK1 sK2 X2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X2) = ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l54 sK1 sK2 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l58 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l56 sK1 sK2]
    conv => enter [1]; rw [← l48 sK1 sK1 sK2]
  have l59 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l55 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l60 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [l59 sK1 sK2 sK0]
  have l61 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h54069 (sK1 ◇ (sK2 ◇ sK1)) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l60 sK1 sK2 sK0]
  have l62 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((X0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l14 sK1 sK2 (X0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h54069 sK0 X0 (sK0 ◇ sK0)]
  have l63 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l62 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l64 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l63 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l57 sK1 sK2 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1 sK0]
  have l65 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l64 sK1 sK2 sK0]
    conv => enter [1]; rw [← l49 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l66 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l50 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l60 sK1 sK2 sK1]
  have l67 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l66 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l68 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [l67 sK1 sK2]
  have l69 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l68 sK1 sK2]
    conv => enter [1]; rw [← l45 sK1 sK2]
  have l70 : ∀ X0 sK1 sK2 X1 : G, ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (X1 ◇ ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l52 sK1 sK2 X0]
    conv => enter [1]; rw [h54069 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1) X1]
  have l71 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l14 sK1 sK2 sK1 (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l70 X0 sK1 sK2 sK1]
  have l72 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l71 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l73 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l72 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l45 sK1 sK2]
  have l74 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l73 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l69 sK1 sK2]
  have l75 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l65 sK1 sK2 sK0]
    conv => enter [1]; rw [h54069 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l76 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l75 sK1 sK2 sK0 sK0]
  have l77 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l76 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1))]
  have l78 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l77 sK0 sK1 sK2]
    conv => enter [1]; rw [l61 sK1 sK2 (sK0 ◇ sK0) sK0]
  have l79 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l80 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l79 sK0 sK1 sK2]
    conv => enter [1]; rw [← l74 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l80 x y z]

theorem Equation4279_4512_implies_Equation54072 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54072 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK1 sK1]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4279 X0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h4279 X0 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [← h4279 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l9 x y y z y]

theorem Equation4512_54072_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54072 : Equation54072 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54072 X0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54072 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54072 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0 X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54072 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
    conv => enter [1, 2]; rw [← h54072 sK0 sK0 X0]
  have l18 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l18 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l15 sK0]
  have l20 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l19 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h54072 sK0 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54072 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 X0]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54072 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 2, 2]; rw [← l21 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l22 X0 sK0 sK0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0 X0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l16 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h54072 sK0 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54072 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l27 sK0 (X1 ◇ X1)]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l28 X0 X1 sK0]
    conv => enter [1]; rw [← l21 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l29 y z x]

theorem Equation4279_4512_implies_Equation54073 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54073 G := by
  have l0 : ∀ X1 X2 sK2 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK2 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK2 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK2 sK1]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [l0 X1 X0 sK2 sK1]
  have l3 : ∀ sK2 sK1 X1 X2 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X1 X2 X0
    conv => enter [1]; rw [l0 sK2 sK1 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l4 : ∀ sK2 sK1 X1 X2 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 sK1 X1 X2 X0
    conv => enter [1]; rw [l3 sK2 sK1 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l5 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK2 sK1 X1 X2 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK1 X1 X2
    conv => enter [1]; rw [l4 sK2 sK1 X1 X2 sK2]
    conv => enter [1, 2, 2]; rw [h4279 sK2 (sK1 ◇ sK2) sK2]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
  have l8 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK2 sK1 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l1 sK2 sK1 sK0]
  have l9 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l8 sK0 sK1 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK0 (sK1 ◇ sK0)]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_54073_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54073 : Equation54073 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54073 ((sK0 ◇ sK0) ◇ X0) sK0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (sK2 ◇ X1)) = (sK2 ◇ ((sK1 ◇ X0) ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [h54073 X1 sK2 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 X0]
  have l11 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54073 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK2 ◇ sK1)]
  have l12 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (sK2 ◇ X1)) = (sK2 ◇ (sK1 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l10 X1 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK2 ◇ sK1) ◇ X0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54073 X0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l15 : ∀ X1 sK2 sK1 X0 : G, (X1 ◇ (sK2 ◇ X1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro X1 sK2 sK1 X0
    conv => enter [1]; rw [l12 X1 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ ((sK2 ◇ sK1) ◇ X0))]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK0 X0]
  have l17 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l11 sK2 sK2 sK1]
    conv => enter [1]; rw [l15 sK2 sK2 sK1 X0]
  have l18 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK0 ◇ X1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54073 X0 X1 (sK0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← l13 sK0 X1]
  have l19 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l13 sK0 X0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l21 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l22 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l19 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l18 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 X1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK0]
  have l28 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l25 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l29 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l26 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l13 sK0 (sK0 ◇ sK0)]
  have l30 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l29 X0 X1 sK0]
    conv => enter [1]; rw [← l28 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l32 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l30 sK0]
  have l33 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l31 X0 X1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l34 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l33 X0 X1 sK0]
    conv => enter [1]; rw [l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l35 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l34 X0 X1 sK0]
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l35 X0 X1 sK0]
    conv => enter [1]; rw [← l22 sK0]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l36 X0 X1 sK0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK0)]
  have l38 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l37 X0 X1 sK0]
    conv => enter [1]; rw [← l32 sK0]
  have l39 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK0)]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l39 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l40 sK0]
  have l42 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK2 ◇ X1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [h54073 X0 X1 (sK2 ◇ X1)]
    conv => enter [1, 2, 2]; rw [l11 X1 sK2 sK1]
  have l43 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ X0) ◇ X1)) = (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l11 X0 sK2 sK1]
  have l44 : ∀ X0 sK2 X1 sK1 : G, (X0 ◇ ((sK2 ◇ X0) ◇ X1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X1)) := by
    intro X0 sK2 X1 sK1
    conv => enter [1]; rw [l43 X0 sK2 X1 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X1]
  have l45 : ∀ X0 X1 sK2 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK2 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))))) := by
    intro X0 X1 sK2 sK1
    conv => enter [1]; rw [l42 X0 X1 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 X1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
  have l46 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X1)) = (X0 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [← l44 X0 sK2 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l47 : ∀ sK0 X1 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK2 ◇ (X1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))))) := by
    intro sK0 X1 sK2 sK1
    conv => enter [1]; rw [← l38 sK0 X1 sK0]
    conv => enter [1]; rw [l45 sK0 X1 sK2 sK1]
  have l48 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l47 sK0 sK0 sK2 sK1]
    conv => enter [1]; rw [← l46 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) sK0]
  have l49 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l48 sK0 sK2 sK1]
    conv => enter [1]; rw [← l17 sK2 sK1 (sK2 ◇ sK1)]
  have l50 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK1]
    conv => enter [1]; rw [← l49 sK0 sK2 sK1]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [← l50 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l51 x y z]

theorem Equation4279_4512_implies_Equation54074 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54074 G := by
  have l0 : ∀ X0 X1 X3 X4 : G, (X0 ◇ (X1 ◇ X0)) = (X3 ◇ (X4 ◇ X3)) := by
    intro X0 X1 X3 X4
    conv => enter [1]; rw [← h4279 X0 X0 X1]
    conv => enter [1]; rw [h4279 X0 X3 X4]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X1) X3]
    conv => enter [1, 1]; rw [← h4279 X0 X1 X2]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X2 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 X1 X3]
  have l5 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X3 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l5 X1 X2 X3 X3 X1]
    conv => enter [1, 2]; rw [← h4279 X0 X3 X1]
  have l7 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [l6 X3 X4 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x y x x w]
  conv => enter [1]; rw [l4 x w y z]

theorem Equation4512_54074_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54074 : Equation54074 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ X2 sK0 X0 X1 : G, (X2 ◇ (sK0 ◇ X2)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X2 sK0 X0 X1
    conv => enter [1]; rw [h54074 X2 sK0 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l8 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = ((sK0 ◇ X1) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [← h54074 (sK0 ◇ X1) X1 X2 X3]
    conv => enter [1, 2]; rw [h54074 X1 sK0 X0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54074 sK0 sK0 X0 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54074 sK0 sK0 X0 sK0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54074 X0 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l4 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l15 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [l8 X1 X2 X3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X1 (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h54074 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK0 X0 X1]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54074 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l6 sK0 sK0]
  have l19 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l15 X1 X2 X3 sK0 X1]
    conv => enter [1, 2, 2]; rw [← h54074 (sK0 ◇ sK0) sK0 X1 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1]; rw [← l18 sK0 X0]
  have l21 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l19 X1 X2 X3 sK0]
    conv => enter [1, 2, 2]; rw [← l17 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l20 sK0 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = ((sK0 ◇ X1) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [← h54074 (sK0 ◇ X1) X1 X2 X3]
    conv => enter [1, 2]; rw [h54074 X1 sK0 X0 (sK0 ◇ sK0)]
  have l26 : ∀ X1 X2 X3 sK0 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X1 X2 X3 sK0 X0
    conv => enter [1]; rw [l25 X1 X2 X3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X1 (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l27 : ∀ X1 X2 X3 sK0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X3))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 X3 sK0
    conv => enter [1]; rw [l26 X1 X2 X3 sK0 X1]
    conv => enter [1]; rw [l21 sK0 X1 (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l28 : ∀ sK0 X1 X2 X3 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l27 X1 X2 X3 sK0]
  have l29 : ∀ sK0 X1 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0 X1 X2 X3]
  have l30 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l29 sK0 X1 X2 X3]
  have l31 : ∀ sK0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (X1 ◇ X3))) := by
    intro sK0 X1 X2 X3
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [l30 sK0 X1 X2 X3]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 X1 sK0 sK0]
    conv => enter [1]; rw [← h54074 X0 X1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l32 x y z]

theorem Equation4279_4512_implies_Equation54076 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54076 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y y z z]

theorem Equation4512_54076_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54076 : Equation54076 G) : Equation4279 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54076 X0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54076 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54076 X0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54076 X0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l9 X0 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 sK0 sK0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ (X1 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 (X1 ◇ (X1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h54076 X0 (sK0 ◇ sK0) X1]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (sK0 ◇ sK0)) (X0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (sK0 ◇ sK0) (X0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l19 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l18 sK0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 sK0]
  have l20 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l19 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l14 sK0]
  have l21 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l20 sK0 X1]
    conv => enter [1, 2, 2]; rw [← l15 sK0]
  have l22 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X1) ◇ X0)) = ((sK0 ◇ X1) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54076 X0 (sK0 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [← l12 sK0 X1]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ X1) ◇ X0)) = (sK0 ◇ (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l22 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 sK0 X1 (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ X1) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l21 sK0 X1]
    conv => enter [1]; rw [← l25 X0 sK0 X1]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l26 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X1 X0]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK0 X0 X1]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l28 sK0 X0 X1]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l29 sK0 X0 X1]
  have l31 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54076 X0 X1 sK0]
    conv => enter [1]; rw [← l30 sK0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

theorem Equation4279_4512_implies_Equation54077 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54077 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4279 sK0 sK0 sK1]
    conv => enter [1]; rw [h4279 sK0 sK2 sK2]
  have l1 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4279 sK2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4279 sK2 X1 X0]
  have l2 : ∀ sK2 X1 X2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK2 X1 X2 X0
    conv => enter [1]; rw [h4279 sK2 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4279 X0 X2 X1]
  have l3 : ∀ sK2 X1 X2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK2 X1 X2 X0
    conv => enter [1]; rw [l2 sK2 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK2 ◇ sK2))]
  have l5 : ∀ sK2 X1 X2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))))) := by
    intro sK2 X1 X2
    conv => enter [1]; rw [l3 sK2 X1 X2 sK2]
    conv => enter [1, 2, 2]; rw [h4279 sK2 (sK2 ◇ sK2) sK2]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X1 X2 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X1 X2 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK2 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l0 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l7 sK0 sK1 X1 sK0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation4512_54077_implies_Equation4279 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54077 : Equation54077 G) : Equation4279 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1))) = ((sK0 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h54077 (sK0 ◇ X0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l10 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54077 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54077 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l11 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l15 : ∀ X1 sK0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0
    conv => enter [1]; rw [← l12 X1 X1 sK0]
    conv => enter [1]; rw [l13 X1 X1 sK0]
  have l16 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro sK0 X1
    conv => enter [1, 2]; rw [← l12 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [← l14 sK0 X1 sK0]
  have l17 : ∀ sK0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l16 sK0 X1]
    conv => enter [1, 2]; rw [l12 X1 X1 sK0]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X1]
  have l19 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK2 ◇ sK1)) sK2 sK0]
  have l20 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l12 sK0 X0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [l12 sK0 X0 sK0]
  have l23 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l12 (sK2 ◇ sK1) X0 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l12 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l23 sK1 sK2 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l24 sK0 X0]
    conv => enter [1]; rw [l25 sK0 X0]
  have l29 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l28 sK0 X0]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0]
  have l32 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l33 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l12 sK1 sK2 sK0]
    conv => enter [1]; rw [← l12 (sK0 ◇ (sK0 ◇ sK0)) sK2 sK0]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 sK0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l32 sK1 sK2 sK0]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l33 sK1 sK2 sK0]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l36 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l37 x y z]

theorem Equation4279_4512_implies_Equation54080 (G : Type*) [Magma G] (h4279 : Equation4279 G) (h4512 : Equation4512 G) : Equation54080 G := by
  have l0 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ X1)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h4279 X1 X1 X2]
    conv => enter [1]; rw [h4279 X1 sK1 sK2]
  have l1 : ∀ sK1 sK2 X2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y y z w]

end Semigroup5
