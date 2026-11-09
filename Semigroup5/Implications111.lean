import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53809_54174_54175_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54174 : Equation54174 G) (h54175 : Equation54175 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l9 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l8 sK0 sK1]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l5 sK0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53809 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l20 sK1 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53809 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l21 sK1 X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l9 sK0]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l5 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l39 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l35 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l39 sK0]
  have l42 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54174 X0 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54174 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ sK0)]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 X0]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK1 ◇ sK1)]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l46 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h54174 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l50 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l30 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l51 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l30 sK0 X0]
  have l52 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l51 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l49 sK0 sK1]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l53 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ sK0) X0]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h54174 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h54174 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1]; rw [← l56 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ sK0)]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l62 sK0 sK1]
  have l64 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l42 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l68 sK0 sK1]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l69 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 ((sK1 ◇ sK1) ◇ sK0)]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l71 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 (sK1 ◇ sK1)]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1, 2]; rw [← l47 sK0 sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1)]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l64 sK0 sK1 sK1]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l29 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l77 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l78 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l80 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l79 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0))]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l81 sK0 sK1]
  have l83 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l82 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54175 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l85 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l84 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l83 sK0 sK1]
    conv => enter [1]; rw [← l85 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l86 x y]

theorem Equation4512_53870_54186_54318_54335_implies_Equation54370 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53870 : Equation53870 G) (h54186 : Equation54186 G) (h54318 : Equation54318 G) (h54335 : Equation54335 G) : Equation54370 G := by
  have l0 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h53870 sK0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [h53870 sK2 sK3]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK2 ◇ sK3)]
  have l2 : ∀ sK0 sK2 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) = (sK0 ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK3) (X0 ◇ ((sK2 ◇ sK3) ◇ X0))]
    conv => enter [1, 2]; rw [← h53870 (sK2 ◇ sK3) X0]
  have l3 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0))]
    conv => enter [1, 2]; rw [← h53870 (sK0 ◇ (sK2 ◇ sK3)) X0]
  have l4 : ∀ sK1 sK0 sK2 sK3 X0 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [h54335 sK1 (sK0 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [← l3 sK1 sK0 sK2 sK3 X0]
  have l5 : ∀ sK0 sK2 sK3 X0 : G, (sK0 ◇ ((sK2 ◇ sK3) ◇ X0)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [h54335 sK0 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← l2 sK0 sK2 sK3 X0]
  have l6 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l4 sK1 sK0 sK2 sK3 X0]
  have l7 : ∀ sK0 sK2 sK3 X0 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l5 sK0 sK2 sK3 X0]
  have l8 : ∀ sK1 sK0 sK2 sK3 X0 : G, (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1, 2]; rw [l7 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) (X0 ◇ ((sK2 ◇ sK3) ◇ X0))]
  have l9 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) X0]
    conv => enter [1]; rw [l8 sK1 sK0 sK2 sK3 X0]
  have l10 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [h54186 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l11 : ∀ sK1 sK2 sK3 X0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X0)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) (X0 ◇ X0)]
    conv => enter [1]; rw [← h54186 sK1 X0 (sK2 ◇ sK3)]
  have l12 : ∀ sK1 X0 sK0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X0)) := by
    intro sK1 X0 sK0 sK2 sK3
    conv => enter [1]; rw [h54186 sK1 X0 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) (X0 ◇ X0)]
  have l13 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h53870 X0 X1]
    conv => enter [1]; rw [l10 X2 X0 X1 X3]
    conv => enter [1, 2, 2]; rw [← h53870 X0 X1]
  have l14 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l13 X2 X0 X1 X3]
    conv => enter [1, 2]; rw [← h54335 X3 X0 X1]
  have l15 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [h54335 X2 X0 X1]
    conv => enter [1]; rw [l14 X2 X0 X1 X3]
  have l16 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((X0 ◇ X0) ◇ X1)) = ((sK1 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK3)) (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [l11 sK1 sK2 sK3 X0]
  have l17 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((X0 ◇ X0) ◇ X1)) = (sK1 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 (X0 ◇ X0) X1]
  have l18 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l17 sK1 sK2 sK3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l19 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ (X0 ◇ X1))) = (sK1 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [l18 sK1 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← h54335 sK1 X0 X1]
  have l20 : ∀ sK1 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK3 X0 X1
    conv => enter [1]; rw [h54335 (sK1 ◇ (sK2 ◇ sK3)) X0 X1]
    conv => enter [1]; rw [l19 sK1 sK2 sK3 X0 X1]
  have l21 : ∀ sK1 X0 X1 sK0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK1 X0 X1 sK0 sK2 sK3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l12 sK1 (X0 ◇ X1) sK0 sK2 sK3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l22 : ∀ sK1 X0 X1 sK0 sK2 sK3 : G, (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 X0 X1 sK0 sK2 sK3
    conv => enter [1]; rw [l21 sK1 X0 X1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l15 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) X1 (X0 ◇ X1) X0]
  have l23 : ∀ sK1 sK0 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK0 sK2 sK3 X0 X1
    conv => enter [1]; rw [l15 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) X0 X1 X1]
    conv => enter [1]; rw [← l22 sK1 X0 X1 sK0 sK2 sK3]
  have l24 : ∀ sK1 sK0 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK0 sK2 sK3 X0 X1
    conv => enter [1]; rw [l23 sK1 sK0 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l15 sK1 X1 (X0 ◇ X1) X0]
  have l25 : ∀ sK1 sK0 sK2 sK3 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ X1)) := by
    intro sK1 sK0 sK2 sK3 X0 X1
    conv => enter [1]; rw [l24 sK1 sK0 sK2 sK3 X0 X1]
    conv => enter [1]; rw [← l15 sK1 X0 X1 X1]
  have l26 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h54318 sK0 sK2 sK3]
    conv => enter [1]; rw [l0 sK0 sK2 sK3]
  have l27 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1, 2]; rw [l26 sK0 sK2 sK3]
    conv => enter [1]; rw [← l11 sK1 sK2 sK3 (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [← l26 sK0 sK2 sK3]
  have l28 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ ((X0 ◇ ((sK2 ◇ sK3) ◇ X0)) ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0)))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK2 sK3 (X0 ◇ ((sK2 ◇ sK3) ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h53870 (sK2 ◇ sK3) X0]
  have l29 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) = (sK1 ◇ ((X0 ◇ ((sK2 ◇ sK3) ◇ X0)) ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0)))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l28 sK1 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [l25 sK1 sK0 sK2 sK3 (X0 ◇ ((sK2 ◇ sK3) ◇ X0)) ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0))]
  have l30 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (X0 ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [l15 sK1 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ X0) (X0 ◇ ((sK2 ◇ sK3) ◇ X0))]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2 sK3 X0]
  have l31 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = (sK1 ◇ ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X0))) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l9 sK1 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [← l30 sK1 sK2 sK3 X0 sK0]
  have l32 : ∀ sK1 sK0 sK2 sK3 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ ((sK2 ◇ sK3) ◇ X0)) := by
    intro sK1 sK0 sK2 sK3 X0
    conv => enter [1]; rw [l31 sK1 sK0 sK2 sK3 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) ((sK2 ◇ sK3) ◇ X0)]
  have l33 : ∀ sK1 sK2 sK3 X0 sK0 : G, (sK1 ◇ ((sK2 ◇ sK3) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [← l20 sK1 sK2 sK3 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [← l32 sK1 sK0 sK2 sK3 X0]
  have l34 : ∀ sK1 sK2 sK3 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK3)) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ X0) := by
    intro sK1 sK2 sK3 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK3) X0]
    conv => enter [1]; rw [l33 sK1 sK2 sK3 X0 sK0]
  have l35 : ∀ X0 sK2 sK3 : G, (X0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK3
    conv => enter [1, 2]; rw [← l1 sK2 sK3]
    conv => enter [1]; rw [← h54335 X0 sK2 sK3]
  have l36 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK2 ◇ sK3)) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← l35 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l37 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [← l35 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l38 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l6 sK1 sK0 sK2 sK3 (sK2 ◇ sK3)]
    conv => enter [1, 2, 2]; rw [← l36 sK0 sK2 sK3]
  have l39 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) = (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l38 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l25 sK1 sK0 sK2 sK3 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3))]
  have l40 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l39 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3))]
  have l41 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l27 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l40 sK1 sK0 sK2 sK3]
  have l42 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l41 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [← l34 sK1 sK2 sK3 (sK2 ◇ sK3) sK0]
  have l43 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK3]
    conv => enter [1]; rw [← l42 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l43 x y z w]

theorem Equation53866_54335_implies_Equation54343 (G : Type*) [Magma G] (h53866 : Equation53866 G) (h54335 : Equation54335 G) : Equation54343 G := by
  have l0 : ∀ X1 X0 sK3 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ sK3))) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 sK3 sK2
    conv => enter [1, 2]; rw [h53866 X0 sK3 sK2]
    conv => enter [1]; rw [← h54335 X1 X0 (sK2 ◇ sK3)]
  have l1 : ∀ X1 X0 sK3 sK2 : G, (X1 ◇ (X0 ◇ sK3)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK3))) := by
    intro X1 X0 sK3 sK2
    conv => enter [1]; rw [h54335 X1 X0 sK3]
    conv => enter [1]; rw [l0 X1 X0 sK3 sK2]
  have l2 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1]; rw [h54335 X0 sK2 (sK0 ◇ sK3)]
    conv => enter [1, 2]; rw [← h53866 sK2 sK3 sK0]
  have l3 : ∀ X0 sK2 sK0 sK3 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK3))) = (X0 ◇ (sK2 ◇ sK3)) := by
    intro X0 sK2 sK0 sK3
    conv => enter [1]; rw [l2 X0 sK2 sK0 sK3]
    conv => enter [1]; rw [← l1 X0 sK2 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [← l3 x y w z]

theorem Equation4512_53870_54013_54034_implies_Equation53880 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53870 : Equation53870 G) (h54013 : Equation54013 G) (h54034 : Equation54034 G) : Equation53880 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h54034 (X1 ◇ X0) X2 X0]
    conv => enter [1, 2]; rw [← h54034 X0 X1 X2]
  have l1 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X1 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54034 X0 X1 X2]
  have l2 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l1 X0 X2 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l4 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l2 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l5 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h54013 X0 X1]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X0) X3]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = ((X1 ◇ X0) ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53870 X1 X0]
    conv => enter [1]; rw [← l5 X1 X0 X2]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 (X2 ◇ (X1 ◇ X0))]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l9 X1 X0 X2]
    conv => enter [1]; rw [← l8 X1 X2 X0 X0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation4512_54026_54172_54175_implies_Equation54178 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54026 : Equation54026 G) (h54172 : Equation54172 G) (h54175 : Equation54175 G) : Equation54178 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h54026 (X1 ◇ (X2 ◇ X0)) X3 X0]
    conv => enter [1, 2, 2]; rw [← h54026 X0 X1 X2]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54026 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ X0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h54026 X0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54026 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l5 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54026 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l6 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ X0)) = (X0 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54026 X0 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ (X1 ◇ X0)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h54026 X0 X1 X2]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54026 sK0 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54026 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l10 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54026 sK1 (sK2 ◇ sK1) X0]
  have l11 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [h54026 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ sK1))]
  have l12 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h54026 sK1 sK1 X0]
    conv => enter [1]; rw [l11 sK1 X0 X1]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l16 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ ((X1 ◇ X0) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l17 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X3 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l18 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 X0 X1]
  have l19 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 X0]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l16 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X3]
  have l21 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l17 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X3 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l22 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 X0 X1]
  have l23 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l20 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l24 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l21 X1 X2 X0 X3]
    conv => enter [1, 2, 2]; rw [← l2 X0 X3 X0 X1]
  have l25 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l23 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  have l26 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l24 X1 X2 X0 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ X0) (X3 ◇ (X1 ◇ (X2 ◇ X0)))]
  have l27 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l26 X1 X2 X0 X3]
    conv => enter [1]; rw [← l25 X1 (X2 ◇ X0) (X2 ◇ X0) X3]
  have l28 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l27 X1 X2 X0 X3]
    conv => enter [1]; rw [← h54172 X1 (X2 ◇ X0)]
  have l29 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l28 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X2 ◇ X0)]
  have l30 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X0)))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l29 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h54172 X2 X0]
  have l31 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l13 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (X0 ◇ sK1)]
    conv => enter [1, 2]; rw [l13 sK1 sK2 X0]
  have l33 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l32 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l34 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54026 (sK1 ◇ sK1) X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l13 sK1 sK2 sK1]
  have l35 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l34 sK1 X0 sK1]
  have l36 : ∀ sK1 sK2 X0 : G, (((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l13 sK1 sK2 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) X0]
  have l37 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l36 sK1 sK2 X0]
  have l38 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ sK0) ◇ X1)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [l15 sK0 sK1 X0]
  have l39 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l38 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X1]
  have l40 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l39 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l41 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ sK1)]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l41 sK0 sK1 X0]
  have l43 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← h54175 sK1 (sK2 ◇ sK1)]
  have l44 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l43 sK1 sK2]
  have l45 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l44 sK1 sK2]
    conv => enter [1]; rw [← l37 sK1 sK2 (sK2 ◇ sK1)]
  have l46 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l13 sK1 sK2 sK2]
    conv => enter [1]; rw [l45 sK1 sK2]
  have l47 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54026 (sK1 ◇ (sK2 ◇ sK1)) X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l46 sK1 sK2]
  have l48 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l47 sK1 sK2 X0]
    conv => enter [1]; rw [← l31 sK1 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
  have l49 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54175 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l50 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l33 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l48 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l52 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54026 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l48 sK1 sK2 sK0]
  have l53 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l50 sK0 sK1 sK2 X0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l52 sK0 sK1 sK2 X0]
  have l54 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l55 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l35 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1 X0]
  have l57 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l56 sK0 sK1 X0]
  have l58 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l57 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ (sK1 ◇ sK1)) X1]
  have l59 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l58 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l60 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h54172 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l59 sK0 sK1 X0 X0]
    conv => enter [1]; rw [← l60 sK0 sK1 X0]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X0)]
  have l63 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l62 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l64 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l54 sK0 sK1 sK2]
    conv => enter [1]; rw [← l62 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l64 sK0 sK1 sK2]
  have l66 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l63 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l30 (sK0 ◇ (sK1 ◇ sK1)) X0 X1 X0]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l69 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [h54172 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [← l68 sK0 sK1 (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) sK2]
  have l70 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l69 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l3 X0 sK0 sK1 sK2]
  have l71 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l70 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← l40 sK0 sK1 X0 X0]
  have l72 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l66 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1]; rw [l71 sK0 sK1 sK2 X0]
  have l73 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l68 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l72 sK0 sK1 sK0 X0]
  have l74 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l75 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2]
  have l76 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK2]
    conv => enter [1]; rw [← l74 sK0 sK1]
  have l77 : ∀ sK0 sK1 X0 sK2 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [← l76 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0 X0]
  have l78 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
    conv => enter [1]; rw [l77 sK0 sK1 X0 sK2]
  have l79 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l73 sK0 sK1 X0]
    conv => enter [1]; rw [l78 sK0 sK1 X0 sK2]
  have l80 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l79 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK2]
  have l81 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← l80 sK0 sK1 sK2]
  have l82 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) sK1]
  have l83 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l82 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l84 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l81 sK0 sK1 sK2]
    conv => enter [1]; rw [← l83 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l84 x y z]

theorem Equation4512_53880_54023_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53880 : Equation53880 G) (h54023 : Equation54023 G) : Equation54034 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l1 X2 X0 X1]
    conv => enter [1, 2]; rw [← h53880 X0 (X1 ◇ X2) X1]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53880 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53880 X2 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h53880 X0 X1 X2]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l3 X2 (X0 ◇ X1) X3 X0]
    conv => enter [1, 2, 2]; rw [← h53880 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 X0 X1]
    conv => enter [1, 2]; rw [l4 X0 X1 X2]
  have l7 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [← l4 X0 X2 X3]
    conv => enter [1]; rw [l5 X0 X2 X3 X1]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1]; rw [← l7 X2 X1 X2 X0]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X1 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l8 X2 X0 X1]
    conv => enter [1]; rw [← h54023 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l9 x z y]

theorem Equation4512_54020_54178_implies_Equation54026 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54020 : Equation54020 G) (h54178 : Equation54178 G) : Equation54026 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h54178 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54178 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54020 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l8 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ (X3 ◇ X3)) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X3 X0 X1 X2
    conv => enter [1]; rw [l0 X4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [l0 X0 X1 X0 X3]
    conv => enter [1]; rw [← l5 X2 X0 (X3 ◇ X1) X1]
  have l10 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [h54178 X3 (X1 ◇ (X2 ◇ (X0 ◇ X0))) X0]
    conv => enter [1, 2, 2]; rw [← l7 X0 X1 X2]
  have l11 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l10 X3 X1 X2 X0]
    conv => enter [1, 2]; rw [← l0 (X1 ◇ (X2 ◇ (X0 ◇ X0))) X0 X1 X2]
  have l12 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l11 X3 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l13 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l12 X3 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ X0) (X0 ◇ X0)]
  have l14 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l13 X3 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l15 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l14 X3 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← l9 X2 X0 X0 X0]
  have l16 : ∀ X3 X1 X2 X0 : G, (X3 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X0))) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l15 X3 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h54178 X2 X0 X0]
  have l17 : ∀ X3 X1 X2 X0 : G, (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = (X3 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [← l16 X3 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X0)) (X1 ◇ (X2 ◇ (X0 ◇ X0)))]
  have l18 : ∀ X3 X1 X2 X0 : G, (X3 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X3 X1 X2 X0
    conv => enter [1]; rw [l5 X3 X1 (X2 ◇ (X0 ◇ X0)) (X2 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l17 X3 X1 X2 X0]
  have l19 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X1))))) := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [l8 X0 X1 X0 X3 X4]
    conv => enter [1]; rw [← l5 X2 X0 (X3 ◇ (X4 ◇ X1)) X1]
  have l20 : ∀ X3 X1 X0 X2 : G, (X3 ◇ (X1 ◇ (X0 ◇ X0))) = (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X3 X1 X0 X2
    conv => enter [1]; rw [l19 X3 X1 X0 X2 X0]
    conv => enter [1]; rw [l18 X3 X1 X2 X0]
  have l21 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l7 X2 X0 X1]
    conv => enter [1]; rw [← l20 X2 X0 X2 X1]
  have l22 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l21 X2 X0 X1]
    conv => enter [1]; rw [← h54020 X2 X0]
  intro x y z
  conv => enter [1]; rw [← l22 x y z]

theorem Equation4512_53880_54318_implies_Equation54370 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53880 : Equation53880 G) (h54318 : Equation54318 G) : Equation54370 G := by
  have l0 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h53880 sK0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK3) (sK0 ◇ (sK2 ◇ sK3))]
  have l1 : ∀ sK0 sK1 sK2 sK3 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK1 sK2 sK3
    conv => enter [1]; rw [← h53880 sK0 (sK2 ◇ sK3) sK1]
    conv => enter [1]; rw [l0 sK0 sK2 sK3]
  have l2 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h53880 sK1 (sK0 ◇ (sK2 ◇ sK3)) sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2 sK3]
  have l3 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l2 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) (sK0 ◇ (sK2 ◇ sK3))]
  have l4 : ∀ sK2 sK3 : G, (sK2 ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK3
    conv => enter [1]; rw [h53880 sK2 sK3 sK3]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK2 ◇ sK3)]
  have l5 : ∀ sK2 sK1 sK3 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK1 sK3
    conv => enter [1]; rw [← h53880 sK2 sK3 sK1]
    conv => enter [1]; rw [l4 sK2 sK3]
  have l6 : ∀ sK2 sK0 sK3 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) := by
    intro sK2 sK0 sK3
    conv => enter [1]; rw [← h53880 sK2 sK3 sK0]
    conv => enter [1]; rw [l4 sK2 sK3]
  have l7 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [h53880 sK1 (sK2 ◇ sK3) sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK1 sK3]
  have l8 : ∀ sK1 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK2 sK3
    conv => enter [1]; rw [l7 sK1 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l9 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK0 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [h53880 sK0 (sK2 ◇ sK3) sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK0 sK3]
  have l10 : ∀ sK0 sK2 sK3 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [l9 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l11 : ∀ sK0 sK2 sK3 : G, ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK0 sK2 sK3
    conv => enter [1]; rw [← l0 sK0 sK2 sK3]
    conv => enter [1]; rw [l10 sK0 sK2 sK3]
  have l12 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) (sK0 ◇ (sK2 ◇ sK3))]
    conv => enter [1, 2]; rw [l11 sK0 sK2 sK3]
  have l13 : ∀ sK1 sK0 sK2 sK3 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK0 ◇ (sK2 ◇ sK3))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l12 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK3)) (sK2 ◇ sK3)]
  have l14 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l3 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [l13 sK1 sK0 sK2 sK3]
  have l15 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [h53880 sK2 sK3 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 sK2 sK3]
  have l16 : ∀ sK2 sK3 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← l4 sK2 sK3]
    conv => enter [1]; rw [l15 sK2 sK3 sK1 sK0]
  have l17 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))))) = (sK1 ◇ ((sK2 ◇ sK3) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h53880 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) sK2]
    conv => enter [1, 2]; rw [← l16 sK2 sK3 sK1 sK0]
  have l18 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))))) = ((sK1 ◇ (sK2 ◇ sK3)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [l17 sK1 sK0 sK2 sK3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK3) (sK2 ◇ sK3)]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK3]
    conv => enter [1]; rw [← l18 sK1 sK0 sK2 sK3]
  have l20 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h53880 sK1 (sK0 ◇ (sK2 ◇ sK3)) sK1]
  have l21 : ∀ sK1 sK0 sK2 sK3 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK0 sK2 sK3
    conv => enter [1]; rw [h54318 sK1 sK0 (sK2 ◇ sK3)]
    conv => enter [1]; rw [← l20 sK1 sK2 sK3 sK0]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK3)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h54318 sK1 sK2 sK3]
    conv => enter [1]; rw [← l21 sK1 sK0 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l22 x y z w]

theorem Equation4512_53866_54026_54178_54339_implies_Equation54343 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h54026 : Equation54026 G) (h54178 : Equation54178 G) (h54339 : Equation54339 G) : Equation54343 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h54178 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54178 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h54026 X1 X2 X0]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l5 : ∀ X3 X0 X1 : G, (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l3 X3 X0 X1 X3]
    conv => enter [1, 2]; rw [← h54178 X0 X1 X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l7 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1
    conv => enter [1]; rw [h54339 X3 X0 X1]
    conv => enter [1]; rw [← l5 X3 X0 X1]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l9 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l7 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l10 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l9 X3 X0 X1]
    conv => enter [1]; rw [← l8 X3 X0 X1 X1]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l8 X0 X1 X3 X2]
    conv => enter [1]; rw [← l10 X0 X1 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h53866 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ X2))]
  have l13 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ X2)]
  have l14 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
    conv => enter [1]; rw [l11 X0 X1 X0 (X3 ◇ X2)]
  have l15 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l14 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l16 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l15 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X3 ◇ X2))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l11 X0 X1 X0 X2]
    conv => enter [1]; rw [← l16 X0 X1 X3 X2]
  intro x y z w
  conv => enter [1]; rw [l17 x y z w]

theorem Equation53812_53869_implies_Equation53879 (G : Type*) [Magma G] (h53812 : Equation53812 G) (h53869 : Equation53869 G) : Equation53879 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53869 sK0 X0]
    conv => enter [1]; rw [← h53812 sK0 X0]
  have l1 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h53812 sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l1 x z y]

theorem Equation4512_53809_54209_implies_Equation54215 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54209 : Equation54209 G) : Equation54215 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54209 X0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

theorem Equation4512_53812_53863_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53863 : Equation53863 G) : Equation53888 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53812 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53863 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h53863 sK2 sK1]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 sK1]
  have l7 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l9 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l7 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) sK1 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l11 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [h53863 sK1 X0]
    conv => enter [1]; rw [← l9 sK2 sK1 (sK1 ◇ (X0 ◇ X0))]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53812 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l9 sK2 sK1 sK1]
  have l13 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1, 2]; rw [← l7 sK2 sK1]
  have l14 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l11 sK2 sK1 X0]
    conv => enter [1]; rw [← l9 sK2 sK1 (X0 ◇ X0)]
  have l15 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l14 sK2 sK1 X0]
    conv => enter [1]; rw [← l9 sK2 sK1 (sK1 ◇ X0)]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l9 sK2 sK1 X0]
    conv => enter [1]; rw [← l15 sK2 sK1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53863 sK1 X0]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK1 ◇ (X0 ◇ X0))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53812 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← l10 sK0 sK1 (X0 ◇ X0)]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0]
    conv => enter [1]; rw [l21 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l13 sK1 sK2]
  have l24 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l13 sK1 sK2]
  have l25 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l24 sK2 sK1]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l27 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l25 sK2 sK1]
    conv => enter [1]; rw [← l16 sK2 sK1 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK1]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l29 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l7 sK2 sK1]
    conv => enter [1]; rw [← l27 sK2 sK1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l31 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l29 sK2 sK1]
    conv => enter [1]; rw [h53812 (sK2 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l29 sK2 sK1]
  have l32 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l29 sK2 sK1]
    conv => enter [1]; rw [l31 sK2 sK1 X0]
  have l33 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l32 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l30 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l33 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l19 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l34 sK0 sK2 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l43 x y z]

theorem Equation4512_53809_54165_implies_Equation54190 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54165 : Equation54165 G) : Equation54190 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54165 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54165 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53809 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53809 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l11 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l15 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l5 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 (X1 ◇ X0) X1]
    conv => enter [1]; rw [← h54165 X0 (X1 ◇ X0)]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← l5 X0 X1 X2]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X3]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l20 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l18 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← l19 X1 X0]
  have l22 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l20 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
  have l23 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l22 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l24 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l23 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l25 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l19 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l26 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0))) X2]
  have l27 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l26 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
  have l28 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l25 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l29 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l27 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l30 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l29 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X0 X2]
  have l31 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l30 X0 X2 X1]
  have l32 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l31 X0 X2 X1]
  have l33 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
    conv => enter [1]; rw [l4 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l34 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54165 X0 X1]
    conv => enter [1]; rw [l4 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h54165 X0 X1]
  have l35 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l4 X3 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← l4 X0 X1 X2]
  have l36 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X1]
    conv => enter [1]; rw [← l4 X0 X1 X0]
  have l37 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53809 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← l4 (X0 ◇ X1) X0 X1]
  have l38 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l4 X0 X1 X2]
  have l39 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l4 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ X3)))]
  have l40 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [l39 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l41 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l38 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))]
  have l42 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l37 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l43 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l33 X3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l44 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l41 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X2) (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))]
  have l45 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l42 X0 X1]
  have l46 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l44 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))]
  have l47 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l45 X0 X1]
  have l48 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ X2)) (X0 ◇ (X1 ◇ (X1 ◇ X2)))]
    conv => enter [1]; rw [l46 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) (X0 ◇ (X1 ◇ (X1 ◇ X2)))]
  have l49 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1 X1]
    conv => enter [1]; rw [l47 X0 X1]
  have l50 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l48 X0 X1 X2]
    conv => enter [1, 2]; rw [← l35 X1 X2 X0 ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))]
  have l51 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l50 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l14 X0 (X1 ◇ (X1 ◇ X2)) (X1 ◇ (X1 ◇ X2))]
  have l52 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l51 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l35 X0 X0 X1 X2]
  have l53 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l52 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← l4 X0 X1 X2]
  have l54 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) = (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l53 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))]
  have l55 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l32 X0 (X1 ◇ (X1 ◇ X2)) (X1 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l54 X0 X1 X2]
  have l56 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l35 X0 X0 X1 X2]
    conv => enter [1]; rw [l55 X0 X1 X2]
  have l57 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l56 X0 X1 X2]
  have l58 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 (X0 ◇ (X0 ◇ X1)) X0 X1]
    conv => enter [1]; rw [l36 (X0 ◇ (X0 ◇ X1)) X2]
  have l59 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2, 2]; rw [← l36 X0 X1]
  have l60 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l34 (X1 ◇ X0) X0 X0]
    conv => enter [1]; rw [← l59 X1 X0]
  have l61 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l58 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l62 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l60 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 ((X1 ◇ X0) ◇ (X1 ◇ X0))]
  have l63 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l61 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l64 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l62 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l65 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l63 X0 X1 X2]
    conv => enter [1]; rw [← l35 X0 X1 X2 (X0 ◇ (X0 ◇ X1))]
  have l66 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l64 X1 X0]
    conv => enter [1]; rw [← l32 X1 X0 X0]
  have l67 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l65 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l4 X2 X0 X1]
  have l68 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l66 X1 X0]
  have l69 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l67 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
  have l70 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53809 X0 X0]
    conv => enter [1]; rw [l68 X1 X0]
  have l71 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l69 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l72 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l24 X0 X1 X1 X0]
    conv => enter [1]; rw [← l71 X0 X1 X2]
  have l73 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l57 X0 X1 X2]
    conv => enter [1, 2]; rw [← l72 X1 X2 X0]
  have l74 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l5 (X2 ◇ (X0 ◇ X1)) X0 X0]
    conv => enter [1, 2, 2]; rw [← l14 X0 X1 X2]
  have l75 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))]
  have l76 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l75 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ ((X0 ◇ X1) ◇ X2))]
  have l77 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l74 X2 X0 X1]
    conv => enter [1]; rw [← l35 (X2 ◇ (X0 ◇ X1)) X0 X0 X1]
  have l78 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l76 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l79 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l77 X2 X0 X1]
    conv => enter [1]; rw [← l73 (X2 ◇ (X0 ◇ X1)) X0 X1]
  have l80 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l78 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l81 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l79 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ X1) (X0 ◇ (X0 ◇ X1))]
  have l82 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l80 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
  have l83 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l81 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l84 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l82 X0 X1 X3 X2]
    conv => enter [1]; rw [← l32 X0 (X1 ◇ X2) X1]
  have l85 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l83 X2 X0 X1]
    conv => enter [1, 2]; rw [← l49 X0 X1]
  have l86 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = ((X2 ◇ (X0 ◇ X1)) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l73 X2 X0 X1]
    conv => enter [1]; rw [← l85 X2 X0 X1]
  have l87 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ ((X0 ◇ X1) ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l86 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ X1) ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l88 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l87 X2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X2 ◇ (X0 ◇ X1)) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l89 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l88 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) (X2 ◇ (X0 ◇ X1))]
  have l90 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l89 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l91 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l90 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l28 X1 X2 X0]
  have l92 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h53809 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1, 2, 2]; rw [← l2 X0 X1 X2]
  have l93 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l5 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X3 X0]
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1 X2]
  have l94 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l19 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1 X2]
  have l95 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))))]
  have l96 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l95 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l97 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l94 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l98 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l93 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l99 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l92 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l100 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l97 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l101 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l98 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l102 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l99 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l103 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l100 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l104 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l101 X1 X0 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l105 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l102 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l106 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l103 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l107 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l104 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l108 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l105 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l109 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l106 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l110 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l107 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l111 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l108 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l112 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l109 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l113 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l110 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l114 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l111 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← l34 X2 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l115 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l112 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l116 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l113 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l117 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l114 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l118 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l115 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← l43 X2 X0 X1 ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l119 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l116 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l120 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l117 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l121 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l118 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [l84 X0 X1 (X2 ◇ X2) (X2 ◇ X2)]
  have l122 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [← l119 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l123 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l120 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l124 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l121 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← l73 X2 X0 (X1 ◇ (X2 ◇ X2))]
  have l125 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l122 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l126 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l123 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← l15 X2 X0 X1 X2]
  have l127 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l124 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← l34 X0 X1 X2]
  have l128 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l125 X1 X0 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l129 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [l126 X1 X0 X2]
  have l130 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [l127 X1 X0 X2]
  have l131 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l128 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l132 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X2 ◇ X2)) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [l129 X1 X0 X2]
  have l133 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X2 ◇ X2)) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [l130 X1 X0 X2]
  have l134 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l131 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h54165 X2 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l135 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l132 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l136 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l133 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l137 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l134 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l138 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l135 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l139 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l136 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l140 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l137 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l141 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l138 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h54165 X2 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l142 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l139 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h54165 X2 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l143 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l140 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l144 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l141 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l145 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l142 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l146 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l143 X1 X0 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l147 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l144 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l148 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l145 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l149 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l147 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l150 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l148 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l151 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l149 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l152 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l150 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l153 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l146 X1 X0 X2 X3]
    conv => enter [1]; rw [← l151 X1 X0 X2]
  have l154 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l151 X1 X0 X2]
    conv => enter [1]; rw [← l152 X1 X0 X2]
  have l155 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l153 X1 X0 X2 X3]
    conv => enter [1]; rw [l154 X1 X0 X2]
  have l156 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l21 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l2 X0 X1 X2]
  have l157 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l21 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0 X1 X2]
  have l158 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l157 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l159 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l156 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))]
  have l160 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l158 X1 X0 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l161 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l159 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))]
  have l162 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 X2 (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [← l160 X1 X0 X2]
  have l163 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l161 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))]
  have l164 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l70 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← l162 X1 X0 X2]
  have l165 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l163 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))]
  have l166 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l164 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← l34 X2 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l167 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l165 X0 X1 X2 X3]
    conv => enter [1]; rw [← l40 X0 X1 X2 (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))]
  have l168 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l166 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l169 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l167 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l170 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l168 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l171 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l169 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l172 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l170 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
  have l173 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l171 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l174 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l172 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← l15 X2 X0 X1 X2]
  have l175 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l173 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← l43 X2 X0 X1 ((X2 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
  have l176 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l24 X1 (X2 ◇ X2) X1 X0]
    conv => enter [1]; rw [l174 X1 X0 X2]
  have l177 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l175 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [← h4512 X2 X2 (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l178 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l34 X1 X1 X2]
    conv => enter [1]; rw [l176 X1 X2 X0]
  have l179 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l177 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← l40 X0 X1 X2 (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
  have l180 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h54165 X1 X2]
    conv => enter [1]; rw [l178 X1 X2 X0]
  have l181 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l70 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))]
    conv => enter [1]; rw [l179 X0 X1 X2 X3]
  have l182 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l180 X1 X2 X0]
    conv => enter [1]; rw [l154 X1 X0 X2]
  have l183 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l43 X0 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l181 X0 X1 X2 X3]
  have l184 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))))))))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l182 X1 X2 X0]
    conv => enter [1]; rw [← l155 X1 X0 X2 X3]
  have l185 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l14 X0 (X1 ◇ (X2 ◇ X2)) X1]
    conv => enter [1]; rw [l183 X0 X1 X2 X3]
  have l186 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [l34 X0 X1 X2]
    conv => enter [1]; rw [l185 X0 X1 X2 X3]
  have l187 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l34 X0 X1 X2]
    conv => enter [1]; rw [l186 X0 X1 X2 X3]
  have l188 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ X4)) = (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X4 X0 X1 X2 X3
    conv => enter [1]; rw [l15 X4 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l189 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l187 X0 X1 X2 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l188 X2 X0 X0 X1 X2]
  have l190 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l184 X1 X2 X0 X1]
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [← l188 X2 X1 X0 X1 X2]
  have l191 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l189 X0 X1 X2]
    conv => enter [1]; rw [← l96 X0 X1 X2 X2]
  have l192 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l190 X1 X2 X0]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← l191 X0 X1 X2]
  have l193 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l192 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l188 X2 X1 X0 X1 X2]
  have l194 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l193 X1 X2 X0]
    conv => enter [1, 2]; rw [← l191 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l194 x y z]
  conv => enter [1, 2, 2]; rw [l194 x y (y ◇ y)]
  conv => enter [1, 2, 2]; rw [h4512 x (y ◇ y) (x ◇ (y ◇ y))]
  conv => enter [1, 2]; rw [l194 z (x ◇ (y ◇ y)) y]
  conv => enter [1, 2, 2, 2]; rw [h4512 z (x ◇ (y ◇ y)) (x ◇ (y ◇ y))]
  conv => enter [1, 2, 2, 2]; rw [h4512 (z ◇ (x ◇ (y ◇ y))) x (y ◇ y)]
  conv => enter [1, 2, 2]; rw [l2 y ((z ◇ (x ◇ (y ◇ y))) ◇ x) y]
  conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 ((z ◇ (x ◇ (y ◇ y))) ◇ x) y y]
  conv => enter [1, 2, 2, 2]; rw [h4512 ((z ◇ (x ◇ (y ◇ y))) ◇ x) y ((((z ◇ (x ◇ (y ◇ y))) ◇ x) ◇ y) ◇ y)]
  conv => enter [1, 2, 2]; rw [← l36 y (((z ◇ (x ◇ (y ◇ y))) ◇ x) ◇ y)]
  conv => enter [1]; rw [← l91 x z y]

theorem Equation4512_53812_53862_implies_Equation53879 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53862 : Equation53862 G) : Equation53879 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53812 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h53812 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53812 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l6 sK0 X0 sK1]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← h53812 sK0 X0]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l10 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l11 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [← h53812 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h53812 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 sK2]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h53812 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 sK2]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53862 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l19 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1, 2]; rw [h53812 sK0 sK2]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53862 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l5 sK0 X0]
  have l21 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0) sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53812 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h53812 sK0 sK2]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l22 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l27 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK2 X0]
    conv => enter [1]; rw [← l26 sK0 sK2 X0]
  have l28 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK2 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK0 X0]
  have l29 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l30 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK2 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l31 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l30 sK0 sK2 X0]
    conv => enter [1]; rw [← l10 sK0 X0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l29 sK0 sK2 sK1]
    conv => enter [1]; rw [← h53862 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK0)]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h53812 sK0 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l31 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l37 sK0 sK2 sK1]
    conv => enter [1]; rw [← h53862 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l39 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l36 sK0 sK2 sK1]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2]
  have l41 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l40 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l42 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK2 X0]
    conv => enter [1]; rw [l41 sK0 sK2 X0 sK1]
  have l43 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l42 sK0 sK2 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l44 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l43 sK0 sK2 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 (sK0 ◇ sK0)]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1 sK0]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l46 x y z]

theorem Equation4512_53809_54202_implies_Equation54215 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54202 : Equation54202 G) : Equation54215 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53809 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← h54202 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [h54202 sK2 sK0]
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54202 sK2 sK0]
  have l22 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h54202 sK2 sK0]
    conv => enter [1]; rw [← l21 sK0 sK2]
  have l23 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l20 sK0 sK2]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK2 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l22 sK2 sK0]
    conv => enter [1]; rw [l23 sK0 sK2 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53809 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l19 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1 X0]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l24 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l29 y z x]

theorem Equation4512_54034_54060_54088_implies_Equation54071 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54034 : Equation54034 G) (h54060 : Equation54060 G) (h54088 : Equation54088 G) : Equation54071 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54060 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h54088 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X0)) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X3]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← l5 X2 X1 (X1 ◇ (X2 ◇ X0)) X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← l5 X1 X2 (X2 ◇ X0) X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X2 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← l5 X2 X1 X0 X1]
  intro x y z
  conv => enter [1]; rw [h54034 x y z]
  conv => enter [1]; rw [l8 x z y]

theorem Equation4512_54022_54026_implies_Equation54027 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54022 : Equation54022 G) (h54026 : Equation54026 G) : Equation54027 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h54022 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h54026 X0 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

theorem Equation4512_53812_53822_53870_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53822 : Equation53822 G) (h53870 : Equation53870 G) : Equation53832 G := by
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
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53812 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53812 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53812 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53822 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53822 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK1 sK0 X0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53812 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h53870 sK1 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l19 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l20 x y]

theorem Equation4512_53808_53809_54172_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53809 : Equation53809 G) (h54172 : Equation54172 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53808 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53808 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 X0]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X1]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l12 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1]; rw [l11 sK0 X1 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) = (sK0 ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54172 sK0 X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0 X0]
    conv => enter [1]; rw [← l14 sK0 X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation4512_53832_53860_53880_implies_Equation53968 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53832 : Equation53832 G) (h53860 : Equation53860 G) (h53880 : Equation53880 G) : Equation53968 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53832 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l2 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l4 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [h53832 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0)) = (((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l1 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l5 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l7 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l6 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l8 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l7 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h53860 (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53832 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK1]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53832 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  have l12 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1 ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK2 sK0 sK1]
  have l14 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l10 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l15 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53880 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) sK2]
  have l17 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK2 sK0 sK1]
    conv => enter [1]; rw [← l16 sK2 sK0 sK1]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l12 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53880 sK0 ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53880 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ X0)]
    conv => enter [1]; rw [← h53880 sK0 X0 sK1]
  have l21 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1 ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l21 sK2 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK2 sK1]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53880 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l23 sK2 sK0 sK1]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [l17 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1 sK2]
  have l26 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h53880 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h53880 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation4512_54176_54178_implies_Equation54179 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54176 : Equation54176 G) (h54178 : Equation54178 G) : Equation54179 G := by
  have l0 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [h54176 X1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) X0]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54178 X0 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) sK1]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53812_53815_53822_53825_53832_54172_implies_Equation54261 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53815 : Equation53815 G) (h53822 : Equation53822 G) (h53825 : Equation53825 G) (h53832 : Equation53832 G) (h54172 : Equation54172 G) : Equation54261 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53812 X0 X1]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53812 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h53812 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [l0 sK1 sK1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 X0]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l11 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l9 sK1]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l13 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l11 sK1]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l13 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l14 sK1 X0]
  have l16 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53812 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [← l6 sK1 X0]
  have l18 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l17 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X1]
  have l19 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ ((X0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l15 sK1 X1]
    conv => enter [1]; rw [← l18 sK1 X0 X1]
  have l20 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l19 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK1) X1]
  have l21 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((X0 ◇ (X1 ◇ (sK1 ◇ sK1))) ◇ X2)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X2) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h4512 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) X2]
    conv => enter [1, 1]; rw [← l16 sK1 X0 X1]
  have l22 : ∀ sK1 X0 X1 X2 : G, (sK1 ◇ ((X0 ◇ (X1 ◇ (sK1 ◇ sK1))) ◇ X2)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X2)) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l21 sK1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X2]
  have l23 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X2)) = (sK1 ◇ (X0 ◇ ((X1 ◇ (sK1 ◇ sK1)) ◇ X2))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [← l22 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ sK1)) X2]
  have l24 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X2)) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X2)))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l23 sK1 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK1 ◇ sK1) X2]
  have l25 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h53815 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l26 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))) = (((sK1 ◇ sK1) ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53815 ((sK1 ◇ sK1) ◇ X0) X0]
    conv => enter [1, 2, 2]; rw [← l25 X0 sK1]
  have l27 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l26 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l28 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l27 sK1 X0]
    conv => enter [1, 2]; rw [← l12 X0 X0 X0]
  have l29 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [l28 sK1 X0]
    conv => enter [1, 2]; rw [← h54172 X0 X0]
  have l30 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (((sK1 ◇ sK1) ◇ X0) ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53822 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l29 sK1 X0]
  have l31 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l30 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) X0 (((sK1 ◇ sK1) ◇ X0) ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l32 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro X0 sK1
    conv => enter [1]; rw [l31 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK1) X0 ((sK1 ◇ sK1) ◇ X0)]
  have l33 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l32 X0 sK1]
    conv => enter [1]; rw [← l20 sK1 (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) X0]
  have l34 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l33 X0 sK1]
    conv => enter [1]; rw [← l24 sK1 X0 (sK1 ◇ sK1) X0]
  have l35 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53825 X1 X0]
    conv => enter [1]; rw [h53822 X1 X2]
    conv => enter [1, 2]; rw [h53825 X1 X0]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53825 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l37 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 X0 X1]
    conv => enter [1]; rw [l35 X0 X1 X2]
    conv => enter [1, 2]; rw [← h54172 X0 X1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l36 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h53812 sK1 sK1]
    conv => enter [1, 2]; rw [← l40 sK0 sK1]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l44 sK1 sK0]
  have l46 : ∀ X0 X1 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h53832 X1 X0]
    conv => enter [1]; rw [l34 X1 sK1]
  have l47 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l46 X0 X1 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 X1]
  have l48 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l37 X0 X1 X0]
    conv => enter [1]; rw [l47 X0 X1 sK0 sK1]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l48 X0 sK1 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l49 z y x]

theorem Equation53813_53870_implies_Equation53881 (G : Type*) [Magma G] (h53813 : Equation53813 G) (h53870 : Equation53870 G) : Equation53881 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53813 X0 X1]
    conv => enter [1]; rw [← h53870 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [h53813 x z]

theorem Equation4512_53842_53846_54209_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53842 : Equation53842 G) (h53846 : Equation53846 G) (h54209 : Equation54209 G) : Equation53850 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54209 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53846 X2 X0 X1]
    conv => enter [1]; rw [h53842 X2 X3 X2]
    conv => enter [1, 2]; rw [h53846 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [← l5 X1 X0 X2 X1]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53846 X2 X1 X0]
    conv => enter [1]; rw [← l6 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_53819_53869_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53819 : Equation53819 G) (h53869 : Equation53869 G) : Equation53817 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h53819 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1 X0]
    conv => enter [1, 2]; rw [← h53869 X0 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53809_53822_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h53822 : Equation53822 G) : Equation53835 G := by
  have l0 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53822 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l0 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l3 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0 X0 X0]
    conv => enter [1, 2]; rw [← l2 X0 X1 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← l2 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_53808_53812_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53812 : Equation53812 G) : Equation53816 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53808 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l2 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53808 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← l5 sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53812 sK0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_53809_53870_53900_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h53870 : Equation53870 G) (h53900 : Equation53900 G) : Equation53838 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53870 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53870 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [← l1 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h53900 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53900 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h53870 X1 X2]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l12 X0 X1 X2]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3)))) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l13 (X1 ◇ X2) X0 X3]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ X3))]
  have l15 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) = (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ X3)))) := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [← l14 X0 X1 X2 X3]
  have l16 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [l15 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ X3))]
  have l17 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X3))))) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l5 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l16 X1 X2 X0 X3]
  have l18 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1]; rw [l17 X1 X2 X0 X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X2 X1]
    conv => enter [1]; rw [← l10 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4512_53812_53816_54164_54172_implies_Equation53820 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53816 : Equation53816 G) (h54164 : Equation54164 G) (h54172 : Equation54172 G) : Equation53820 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53812 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54164 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54164 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54172 X0 X1]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54172 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l7 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2]; rw [l6 X0 X1 X2]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← h54164 X0 X1]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l11 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l13 X2 X0 X1]
    conv => enter [1]; rw [l11 X2 X0 (X1 ◇ (X2 ◇ X0))]
  have l16 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h53816 X3 X0]
    conv => enter [1, 2]; rw [l12 X0 X1 X2]
  have l17 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l16 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← l15 X0 X1 X2]
  have l18 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l17 X2 X3 X0 X1]
    conv => enter [1, 2, 2]; rw [← h54164 X0 X1]
  have l19 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ X3)) = (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l18 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [l6 X0 X1 X2]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2 X0]
    conv => enter [1]; rw [← l14 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation4512_53850_53900_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53850 : Equation53850 G) (h53900 : Equation53900 G) : Equation53838 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h53900 X0 X1]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53850 X2 X0 X1]
    conv => enter [1]; rw [h53850 X2 X3 X2]
    conv => enter [1, 2]; rw [h53850 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X1]
    conv => enter [1]; rw [← l4 X0 X1 X2]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53850 X2 X0 X1]
    conv => enter [1]; rw [l6 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation53817_54164_implies_Equation53820 (G : Type*) [Magma G] (h53817 : Equation53817 G) (h54164 : Equation54164 G) : Equation53820 G := by
  intro x y z
  conv => enter [1]; rw [h53817 x y (z ◇ y)]
  conv => enter [1, 2]; rw [← h54164 y z]

theorem Equation4512_53822_53825_53900_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53822 : Equation53822 G) (h53825 : Equation53825 G) (h53900 : Equation53900 G) : Equation53838 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53900 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ X2)))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X1 ◇ X2)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53825 X1 X0]
    conv => enter [1]; rw [h53822 X1 X2]
    conv => enter [1, 2]; rw [h53825 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← l2 X1 X2 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← l2 X1 X2 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [← l2 X1 X2 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [← h53825 X2 X1]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

theorem Equation4512_53808_53813_53816_54164_implies_Equation53820 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53808 : Equation53808 G) (h53813 : Equation53813 G) (h53816 : Equation53816 G) (h54164 : Equation54164 G) : Equation53820 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54164 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [h53816 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l4 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h53808 X1 X2]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h53813 X0 X1]
    conv => enter [1]; rw [h53813 X0 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X0]
    conv => enter [1]; rw [l8 X0 X0 X2]
  have l11 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X2)) X3]
    conv => enter [1, 1]; rw [← l10 X0 X1 X2]
  have l12 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l11 X0 X2 X3 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
  have l13 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l12 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l14 : ∀ X0 X2 X3 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l13 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l15 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X2 X3 X1
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X2) X3]
    conv => enter [1]; rw [l14 X0 X2 X3 X1]
  have l16 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l15 X0 X2 X3 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l17 : ∀ X0 X1 X3 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h53808 X0 (X0 ◇ X3)]
    conv => enter [1]; rw [← l16 X0 X1 X3 X0]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l2 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l18 x y z]

theorem Equation53825_53870_implies_Equation53959 (G : Type*) [Magma G] (h53825 : Equation53825 G) (h53870 : Equation53870 G) : Equation53959 G := by
  intro x y z
  conv => enter [1]; rw [h53870 x y]
  conv => enter [1]; rw [← h53825 y x]
  conv => enter [1]; rw [h53825 y z]

theorem Equation53813_54172_implies_Equation54183 (G : Type*) [Magma G] (h53813 : Equation53813 G) (h54172 : Equation54172 G) : Equation54183 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53813 X0 X1]
    conv => enter [1]; rw [← h54172 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [h53813 x z]

theorem Equation4512_53828_53900_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53828 : Equation53828 G) (h53900 : Equation53900 G) : Equation53850 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h53828 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l0 x y z x]
  conv => enter [1, 2]; rw [← h53900 z x]

theorem Equation4512_53810_53814_54164_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53810 : Equation53810 G) (h53814 : Equation53814 G) (h54164 : Equation54164 G) : Equation53817 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h54164 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X2]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [h53810 x x]
  conv => enter [1, 2]; rw [h53814 x y z]
  conv => enter [1]; rw [← l4 x y z]

theorem Equation4512_53818_53870_54186_54190_implies_Equation54168 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53818 : Equation53818 G) (h53870 : Equation53870 G) (h54186 : Equation54186 G) (h54190 : Equation54190 G) : Equation54168 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [h53818 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (X1 ◇ sK2))]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h54190 sK1 sK2 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
  have l3 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h53818 sK2 X0 sK1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 X0 sK1]
  have l6 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [h53818 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [h53818 sK2 X0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK2 ◇ sK2))]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l5 sK2 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ sK2)]
  have l10 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l5 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (X0 ◇ (sK1 ◇ sK2))]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l10 sK1 sK2 X0]
  have l12 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1]
  have l13 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1]
  have l14 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l5 sK2 sK0 sK1]
    conv => enter [1]; rw [h53818 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [l5 sK2 sK0 sK1]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l16 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l17 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l12 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l18 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 sK1]
    conv => enter [1]; rw [← l15 sK2 sK0 sK1]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK1 ◇ sK2)]
  have l20 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l16 sK1 sK2 sK0]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK0 ◇ (sK2 ◇ sK2)) ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h53818 (sK1 ◇ sK2) X0 (sK0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l20 sK0 sK2 sK1]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l23 sK1 sK2 sK1 sK1]
  have l25 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← l11 sK1 sK2 (sK1 ◇ sK2)]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53870 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l26 sK0 sK1 sK2]
  have l28 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [l16 sK1 sK2 sK0]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l28 sK1 sK2 sK0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) sK2]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0]
  have l33 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l8 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (sK2 ◇ sK2))]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1]; rw [l33 sK0 sK1 sK2 X0]
  have l35 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [l34 sK0 sK1 sK2 X0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l36 sK0 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l18 sK2 sK0 sK1]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
  have l40 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1, 2]; rw [l36 sK0 sK1 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h54186 X0 (sK2 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
  have l41 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l40 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 sK2]
  have l42 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l41 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h54186 X0 sK2 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
    conv => enter [1]; rw [l42 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l43 x z y]

theorem Equation4512_53818_53873_53888_54172_implies_Equation53884 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53818 : Equation53818 G) (h53873 : Equation53873 G) (h53888 : Equation53888 G) (h54172 : Equation54172 G) : Equation53884 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = (X3 ◇ (X3 ◇ X0)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [← h53818 X0 X1 X2]
    conv => enter [1]; rw [← h53873 X3 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l3 X1 X2 X0 X1]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h53888 X0 X2 X1]
    conv => enter [1]; rw [l4 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53818_53822_54172_implies_Equation53842 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53818 : Equation53818 G) (h53822 : Equation53822 G) (h54172 : Equation54172 G) : Equation53842 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54172 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h53818 X0 X1 X2]
    conv => enter [1]; rw [h53822 X0 X3]
    conv => enter [1, 2]; rw [h53818 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← l3 X2 X0 X1 X1]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l3 X2 X0 X1 X0]
    conv => enter [1]; rw [← l4 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [h53818 x y z]
  conv => enter [1]; rw [l5 x y z]

end Semigroup5
