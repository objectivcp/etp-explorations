import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54184_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54184 : Equation54184 G) : Equation53808 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
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
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54184 sK0 (sK0 ◇ sK0) X0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54184 sK0 sK0 X0 sK0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54184 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54184 sK0 X0 (sK0 ◇ sK0) sK0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54184 sK0 X0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 sK1]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54184 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l22 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54184 sK0 (sK0 ◇ sK0) X0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54184 sK0 X0 (sK0 ◇ sK0) sK1]
  have l24 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54184 sK0 (sK0 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54184 sK0 X0 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h54184 sK0 X0 (sK0 ◇ sK1) sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54184 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54184 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l28 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK0)]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1]
  have l47 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [h54184 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0 sK0]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK0]
    conv => enter [1]; rw [← l47 sK0 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1]; rw [← l36 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l55 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l56 x y]

theorem Equation4512_54184_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54184 : Equation54184 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54184 sK0 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation53963_implies_Equation53876 (G : Type*) [Magma G] (h53963 : Equation53963 G) : Equation53876 G := by
  intro x y z
  conv => enter [1]; rw [h53963 x y x z]

@[equational_result]
theorem Equation53963_implies_Equation53951 (G : Type*) [Magma G] (h53963 : Equation53963 G) : Equation53951 G := by
  intro x y z
  conv => enter [1]; rw [h53963 x y z x]

@[equational_result]
theorem Equation53963_implies_Equation53959 (G : Type*) [Magma G] (h53963 : Equation53963 G) : Equation53959 G := by
  intro x y z
  conv => enter [1]; rw [h53963 x y z z]

@[equational_result]
theorem Equation53963_implies_Equation53913 (G : Type*) [Magma G] (h53963 : Equation53963 G) : Equation53913 G := by
  intro x y z
  conv => enter [1]; rw [h53963 x y y z]

theorem Equation4512_53963_implies_Equation4275 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation4275 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_53963_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53888 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h53963 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h53963 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l0 sK0 sK2 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53963 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h53963 sK2 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]
  conv => enter [1]; rw [l1 z y x]

theorem Equation4512_53963_implies_Equation53968 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53968 G := by
  have l0 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h53963 X0 (sK0 ◇ sK1) X1 sK1]
    conv => enter [1, 2]; rw [← h53963 sK0 sK1 (sK0 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53963 sK0 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h53963 sK0 sK1 sK0 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53963_implies_Equation53934 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53934 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h53963 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53963 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53963_implies_Equation53866 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53866 G := by
  have l0 : ∀ X0 sK1 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 X1 X2 sK0
    conv => enter [1]; rw [h53963 X0 sK1 (X1 ◇ X2) sK0]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53963 X0 sK1 sK1 sK0]
  have l2 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h53963 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2 sK0]
  have l4 : ∀ sK2 sK1 sK0 X1 X2 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0 X1 X2
    conv => enter [1]; rw [← l2 sK2 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 sK2 sK1 X1 X2 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ sK2 sK1 sK0 X1 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0 X1
    conv => enter [1]; rw [l4 sK2 sK1 sK0 X1 sK2]
    conv => enter [1, 2]; rw [← h53963 sK2 sK1 sK2 sK0]
  have l7 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h53963 sK2 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
  have l8 : ∀ X1 sK1 sK0 X2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 sK1 sK0 X2 X0
    conv => enter [1]; rw [← h53963 X0 (sK1 ◇ (sK0 ◇ sK1)) X1 X2]
    conv => enter [1, 2]; rw [← h53963 sK0 sK1 X0 sK0]
  have l9 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [← h53963 sK0 sK1 X0 sK0]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53963 sK0 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53963 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h53963 sK2 sK1 sK0 sK0]
  have l13 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l9 X0 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X1]
  have l14 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [← l8 X1 sK1 sK0 X2 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l15 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l12 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [l7 sK2 sK1 sK0]
  have l16 : ∀ X0 sK0 sK1 X2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 X2
    conv => enter [1]; rw [l14 X0 sK0 sK1 X0 X2]
    conv => enter [1]; rw [← l13 sK0 sK1 (X2 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l17 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l16 X0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h53963 sK2 sK1 X0 sK0]
  have l18 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l6 sK2 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l17 X0 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 sK1 sK0 X0]
  have l20 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X1 ◇ ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [h53963 X0 (sK2 ◇ sK1) X1 sK2]
    conv => enter [1, 2, 2]; rw [l7 sK2 sK1 sK0]
  have l21 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [l20 X0 sK2 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 sK1 (sK2 ◇ sK1) sK2]
  have l22 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
    conv => enter [1]; rw [← l21 X0 sK2 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l22 x y x z]

theorem Equation4512_53963_implies_Equation53873 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53873 G := by
  have l0 : ∀ X0 sK1 X1 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h53963 X0 sK1 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l1 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro X1 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 sK1 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y x]

@[equational_result]
theorem Equation53963_implies_Equation53907 (G : Type*) [Magma G] (h53963 : Equation53963 G) : Equation53907 G := by
  intro x y
  conv => enter [1]; rw [h53963 x y y x]

theorem Equation4512_53963_implies_Equation53897 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53897 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53963 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53963 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53963_implies_Equation53863 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53863 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1 X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l7 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53963 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h53963 X0 sK1 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53963 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53963 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53963 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0]
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [l7 (sK0 ◇ sK1) sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

theorem Equation4512_53963_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53828 G := by
  have l0 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53963 sK0 sK0 X0 sK2]
  have l1 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation53963_implies_Equation53870 (G : Type*) [Magma G] (h53963 : Equation53963 G) : Equation53870 G := by
  intro x y
  conv => enter [1]; rw [h53963 x y x x]

theorem Equation4512_53963_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h53963 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53963 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53963_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53850 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53963_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53825 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53963 sK0 sK0 X0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y]

theorem Equation4512_53963_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53838 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ X1 sK2 sK0 X2 X0 : G, (X1 ◇ (X1 ◇ (sK2 ◇ sK0))) = (X2 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK2 sK0 X2 X0
    conv => enter [1]; rw [h53963 X1 (sK2 ◇ sK0) X2 sK2]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK0 sK2]
  have l5 : ∀ X1 sK2 sK0 X2 : G, (X1 ◇ (X1 ◇ (sK2 ◇ sK0))) = (X2 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK2 sK0 X2
    conv => enter [1]; rw [l4 X1 sK2 sK0 X2 X1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 X1]
  have l6 : ∀ X1 sK2 sK0 X2 : G, (X1 ◇ (X1 ◇ (sK2 ◇ sK0))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK2 sK0 X2
    conv => enter [1]; rw [l5 X1 sK2 sK0 X2]
    conv => enter [1, 2]; rw [← l3 sK0 (sK2 ◇ sK0)]
  have l7 : ∀ sK0 X1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X1 sK2
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [← l6 X1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_53963_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53963 sK0 sK0 X0 sK1]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation4512_53963_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53832 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ X1 X2 sK0 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ sK0))) = (X3 ◇ ((X2 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 sK0 X3 X0
    conv => enter [1]; rw [h53963 X1 (X2 ◇ sK0) X3 X2]
    conv => enter [1, 2, 2]; rw [← l1 X0 sK0 X2]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ X1 X2 sK0 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ sK0))) = (X3 ◇ (X2 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X1 X2 sK0 X3 X0
    conv => enter [1]; rw [l2 X1 X2 sK0 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X2 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ X1 X2 sK0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ sK0))) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 X2 sK0 X3
    conv => enter [1]; rw [l5 X1 X2 sK0 X3 X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0 X1]
  have l7 : ∀ X1 X2 sK0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ sK0))) = (X3 ◇ (X2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 sK0 X3
    conv => enter [1]; rw [l6 X1 X2 sK0 X3]
    conv => enter [1, 2, 2]; rw [← l4 sK0 sK0]
  have l8 : ∀ X3 sK0 X1 X2 : G, (X3 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X1 ◇ (X2 ◇ sK0))) := by
    intro X3 sK0 X1 X2
    conv => enter [1, 2]; rw [l4 sK0 X2]
    conv => enter [1]; rw [← l7 X1 X2 sK0 X3]
  have l9 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ (X2 ◇ sK0))) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X1 X2]
  intro x y
  conv => enter [1]; rw [l9 x y x]

theorem Equation4512_53963_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53815 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_53963_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53835 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_53963_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53822 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l0 X0 sK0 X1]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l1 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_53963_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53963 : Equation53963 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h53963 X0 sK0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l11 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [← l10 X0 sK0 X1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l11 X0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l11 X0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2]; rw [← l11 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l9 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l13 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← l21 sK0]
  intro x
  conv => enter [1]; rw [l22 x]

theorem Equation4512_54182_implies_Equation54190 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation54190 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54182 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54182 X2 X2 X0]
    conv => enter [1, 2]; rw [h54182 X0 X2 X1]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54182 (X0 ◇ X1) X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X3)]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) X3 X0]
    conv => enter [1, 2, 2]; rw [← h54182 X0 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h54182 X0 X1 X0]
  have l7 : ∀ X0 X2 X3 X1 X4 : G, (X0 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = ((X0 ◇ (X1 ◇ X1)) ◇ X4) := by
    intro X0 X2 X3 X1 X4
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X3 ◇ (X0 ◇ X1))) X4]
    conv => enter [1, 1]; rw [← l0 X0 X1 X2 X3]
  have l8 : ∀ X0 X2 X3 X1 X4 : G, (X0 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = (X0 ◇ ((X1 ◇ X1) ◇ X4)) := by
    intro X0 X2 X3 X1 X4
    conv => enter [1]; rw [l7 X0 X2 X3 X1 X4]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X4]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X2 X0 X1 X3]
  have l10 : ∀ X0 X2 X3 X1 X4 : G, (X0 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ X4))) := by
    intro X0 X2 X3 X1 X4
    conv => enter [1]; rw [l8 X0 X2 X3 X1 X4]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X4]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h54182 X0 X1 X1]
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
  have l12 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X0 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l10 X0 X2 X3 X1 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ (X0 ◇ X1)) X4]
  have l13 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X0 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l12 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X0 ◇ X1) X4]
  have l14 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l13 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X4]
  have l15 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l4 X0 X1 X3 X0]
    conv => enter [1]; rw [← l14 X0 X1 X3 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h54182 X0 (X1 ◇ X1) X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1 X1 X1]
    conv => enter [1]; rw [← l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← l18 X0 X1]
  have l20 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 (X2 ◇ X0) X0 X2]
    conv => enter [1, 2]; rw [← l1 X0 X2 X1]
  have l21 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((X2 ◇ X0) ◇ (X2 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [← l20 X1 X2 X0]
  have l22 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l21 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X0 (X2 ◇ X0)]
  have l23 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h54182 X2 X0 X0]
    conv => enter [1]; rw [← l22 X1 X0 X2]
  intro x y z
  conv => enter [1]; rw [← l23 x z y]
  conv => enter [1]; rw [l15 x z y]

theorem Equation4512_54182_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation54186 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54182 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) X3 X0]
    conv => enter [1, 2, 2]; rw [← h54182 X0 X1 X2]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h54182 X0 X1 X0]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X2 X0 X1 X3]
  have l4 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h54182 X0 X1 X1]
    conv => enter [1]; rw [l3 X2 X0 X1 X3]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h54182 X0 (X1 ◇ X1) X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X1 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X1 X1]
    conv => enter [1]; rw [← l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [l8 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X0 ◇ (X2 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [← l4 X0 X2 X2 X1]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X2]
    conv => enter [1]; rw [← l10 X0 X1 X2]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l11 X0 X2 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_54182_implies_Equation54162 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation54162 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54182 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y x]

theorem Equation4512_54182_implies_Equation54165 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation54165 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1]; rw [← h54182 sK0 X0 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54182 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54182_implies_Equation54172 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation54172 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [h54182 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation4512_54182_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation54175 G := by
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
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l2 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ X0))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h54182 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54182 X2 X2 X0]
    conv => enter [1, 2]; rw [h54182 X0 X2 X1]
  have l7 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h54182 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h54182 sK1 X0 sK1]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ X0)]
    conv => enter [1]; rw [← h54182 sK1 X0 (sK1 ◇ sK1)]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l1 sK1 X0]
    conv => enter [1]; rw [l8 sK1 X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [l7 sK1 X0]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ X0))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l5 sK1 X0 X1]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [← l11 sK1 X0]
  have l14 : ∀ sK1 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l4 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [l12 sK1 X0 X1]
  have l15 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l4 sK1 X0]
    conv => enter [1]; rw [l14 sK1 X0 X1]
  have l16 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [l15 sK1 X0 X1]
  have l17 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [l16 sK1 X0 X1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l6 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l17 sK1 (X0 ◇ sK1) X0]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l18 sK1 X0]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 X0]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54182 X0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l20 sK1 X0]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation54182_implies_Equation53812 (G : Type*) [Magma G] (h54182 : Equation54182 G) : Equation53812 G := by
  intro x y
  conv => enter [1]; rw [h54182 x x y]

theorem Equation4512_54182_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation53815 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54182 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))) = (X0 ◇ (X1 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← h54182 (X0 ◇ X1) X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X3 ◇ X3)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))) = (X0 ◇ (X1 ◇ (X3 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X0 X2 X3 X1 X4 : G, (X0 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = ((X0 ◇ (X1 ◇ X1)) ◇ X4) := by
    intro X0 X2 X3 X1 X4
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X3 ◇ (X0 ◇ X1))) X4]
    conv => enter [1, 1]; rw [← l0 X0 X1 X2 X3]
  have l5 : ∀ X0 X2 X3 X1 X4 : G, (X0 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = (X0 ◇ ((X1 ◇ X1) ◇ X4)) := by
    intro X0 X2 X3 X1 X4
    conv => enter [1]; rw [l4 X0 X2 X3 X1 X4]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X4]
  have l6 : ∀ X0 X2 X3 X1 X4 : G, (X0 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X1))) ◇ X4)) = (X0 ◇ (X1 ◇ (X1 ◇ X4))) := by
    intro X0 X2 X3 X1 X4
    conv => enter [1]; rw [l5 X0 X2 X3 X1 X4]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X4]
  have l7 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X0 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X1)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l6 X0 X2 X3 X1 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X3 ◇ (X0 ◇ X1)) X4]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X0 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X3 (X0 ◇ X1) X4]
  have l9 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ X4))) = (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X4]
  have l10 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X3 ◇ X3))) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3
    conv => enter [1]; rw [l3 X0 X1 X3 X0]
    conv => enter [1]; rw [← l9 X0 X1 X3 X1 X0]
  intro x y
  conv => enter [1]; rw [h54182 x x y]
  conv => enter [1]; rw [l10 x y x]

theorem Equation4512_54182_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54182 : Equation54182 G) : Equation53807 G := by
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
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l5 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l8 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l15 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54182 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54182 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l4 sK0 X0]
    conv => enter [1]; rw [← h54182 (sK0 ◇ (sK0 ◇ sK0)) X0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h54182 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h54182 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1]; rw [← h54182 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l9 sK0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [h54182 sK0 X1 X0]
  have l29 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X1 ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l28 sK0 X1 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ (sK0 ◇ X1))]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [l26 sK0 X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)]
    conv => enter [1]; rw [l24 sK0 X0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← l31 sK0 X0]
  have l36 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l34 sK0 X0]
  have l38 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l36 sK0]
    conv => enter [1]; rw [l32 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l39 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [← l35 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l39 sK0]
  have l41 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l25 sK0 sK0]
    conv => enter [1]; rw [← l40 sK0]
  have l42 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l41 sK0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l42 sK0]
  have l44 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l43 sK0]
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l45 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l43 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l43 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l47 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l45 sK0]
  have l48 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [l47 sK0]
  have l49 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1]; rw [← l8 sK0]
  have l50 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l46 sK0]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l51 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l37 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l50 sK0]
  have l52 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [l51 sK0]
  have l53 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l48 sK0]
    conv => enter [1]; rw [← l45 sK0]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l49 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l55 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1, 2]; rw [l52 sK0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l56 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l55 sK0]
    conv => enter [1]; rw [← l54 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l57 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l56 sK0]
    conv => enter [1]; rw [← l44 sK0]
  have l58 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l49 sK0]
    conv => enter [1]; rw [← l57 sK0]
  have l59 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l53 sK0]
    conv => enter [1]; rw [← l58 sK0]
  intro x
  conv => enter [1]; rw [l59 x]

theorem Equation4512_53876_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53888 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h53876 X0 X1 X2]
    conv => enter [1]; rw [h53876 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h53876 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h53876 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h53876 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l5 : ∀ X3 X0 X1 : G, (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l2 X3 X0 X1 X3]
    conv => enter [1, 2]; rw [← l1 X0 X1 X3 X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) (X3 ◇ (X1 ◇ (X2 ◇ X1)))]
  have l7 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l1 X1 (X2 ◇ X1) X0 X1]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X3]
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1 X0]
    conv => enter [1, 2]; rw [← h53876 X1 X1 X0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l9 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53876 X0 X1 X1]
    conv => enter [1]; rw [← l10 X0 X1]
  have l13 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [l1 X0 X1 X0 X3]
    conv => enter [1]; rw [l11 X2 X0 X1 (X3 ◇ X1)]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [← l11 X0 X1 X3 X2]
    conv => enter [1]; rw [l5 X0 X1 (X3 ◇ (X1 ◇ X2))]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X3]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [l11 X1 X1 X0 X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l15 X0 X1 X1 X2]
    conv => enter [1]; rw [← l16 X0 X1 X2]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1]; rw [← l13 X0 X0 X2 X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l18 X0 X2 X1]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← l12 X0 X2]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X0 X0 X1]
    conv => enter [1]; rw [l19 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l21 x y z]
  conv => enter [1]; rw [l5 x z y]

theorem Equation4512_53876_implies_Equation53866 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53866 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h53876 X0 X1 X2]
    conv => enter [1]; rw [h53876 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ X2)) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h53876 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [h53876 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h53876 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l5 : ∀ X3 X0 X1 : G, (X3 ◇ (X3 ◇ (X0 ◇ X1))) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X3 X0 X1
    conv => enter [1]; rw [l2 X3 X0 X1 X3]
    conv => enter [1, 2]; rw [← l1 X0 X1 X3 X0]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ (X1 ◇ (X2 ◇ X1)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) (X3 ◇ (X1 ◇ (X2 ◇ X1)))]
  have l7 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l1 X1 (X2 ◇ X1) X0 X1]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X3]
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1 X0]
    conv => enter [1, 2]; rw [← h53876 X1 X1 X0]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X0 ◇ (X0 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l9 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X3]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h53876 X0 X1 X1]
    conv => enter [1]; rw [← l10 X0 X1]
  have l13 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X1)))) := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [l1 X0 X1 X0 X3]
    conv => enter [1]; rw [l11 X2 X0 X1 (X3 ◇ X1)]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [← l11 X0 X1 X3 X2]
    conv => enter [1]; rw [l5 X0 X1 (X3 ◇ (X1 ◇ X2))]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
    conv => enter [1]; rw [l5 X0 X1 X3]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [l11 X1 X1 X0 X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l15 X0 X1 X1 X2]
    conv => enter [1]; rw [← l16 X0 X1 X2]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1]; rw [← l13 X0 X0 X2 X1]
  have l19 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X2 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [l18 X0 X2 X1]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← l12 X0 X2]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l20 X0 X0 X1]
    conv => enter [1]; rw [← l19 X0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l21 x y z]

theorem Equation4512_53876_implies_Equation53873 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53873 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53876 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53876_implies_Equation53863 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53863 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1, 1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53876 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53876 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53876 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK1) sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation4512_53876_implies_Equation53870 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53870 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53876 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53876_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53876 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53876 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (X0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_53876_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53876 sK0 sK0 X0]
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

theorem Equation4512_53876_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53815 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53876 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h53876 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53876 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l9 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h53876 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h53876 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l3 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l10 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 X0 sK0]
  have l14 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l6 X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53876 (sK1 ◇ sK0) (sK0 ◇ sK0) sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53876 (sK0 ◇ sK0) (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l3 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53876 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l17 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [l21 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
  have l28 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l15 sK0 X0]
    conv => enter [1]; rw [l3 sK1 sK0 (X0 ◇ sK0)]
  have l32 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l31 sK1 sK0 X0]
    conv => enter [1]; rw [← l30 sK1 sK0 (X0 ◇ sK0)]
  have l33 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0 sK1]
    conv => enter [1]; rw [← l28 sK1 sK0 sK1]
  have l34 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [l33 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 (sK0 ◇ sK0)]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53876 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l38 sK0 sK1]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ sK0) X0]
  have l41 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l25 sK1 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l42 sK1 sK0]
  have l48 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53876 X0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l42 sK1 sK0]
  have l49 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l13 X0 sK0]
    conv => enter [1]; rw [l48 X0 sK0 sK1]
  have l50 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l46 sK1 sK0]
  have l51 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l34 sK1 sK0]
    conv => enter [1]; rw [← l50 sK1 sK0]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l49 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53876 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l57 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l58 x y]

theorem Equation4512_53876_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53876 : Equation53876 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53876 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation54331_implies_Equation54335 (G : Type*) [Magma G] (h54331 : Equation54331 G) : Equation54335 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54331 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h54331 sK1 X0 sK2]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1]; rw [← h54331 X0 sK1 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_54331_implies_Equation54020 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54331 : Equation54331 G) : Equation54020 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← h54331 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54331_implies_Equation54172 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54331 : Equation54331 G) : Equation54172 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54331 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation4512_54352_implies_Equation54335 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54352 : Equation54352 G) : Equation54335 G := by
  have l0 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h54352 X0 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54352 (sK1 ◇ sK2) sK1 sK2]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54352 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l2 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54352 X0 sK1 sK2]
    conv => enter [1]; rw [l0 X0 sK2 sK1]
  have l3 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation54352_implies_Equation54013 (G : Type*) [Magma G] (h54352 : Equation54352 G) : Equation54013 G := by
  intro x y
  conv => enter [1]; rw [h54352 x y x]

@[equational_result]
theorem Equation54352_implies_Equation53870 (G : Type*) [Magma G] (h54352 : Equation54352 G) : Equation53870 G := by
  intro x y
  conv => enter [1]; rw [h54352 x x y]

theorem Equation4512_54173_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation54176 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1, 1]; rw [← h54173 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 X3]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54173 X0 X1 (X0 ◇ X2)]
    conv => enter [1]; rw [← l4 X0 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_54173_implies_Equation54171 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation54171 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h54173 sK0 sK0 X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54173 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54173 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54173 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l3 sK1 sK0]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54173 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ X0)]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK1 sK0 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l13 sK0 sK0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK1 ◇ X0)]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ X0) X1]
  have l24 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l25 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l22 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l24 sK0 sK1 X1 sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 (sK0 ◇ sK0)]
  have l27 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l28 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l27 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l25 sK0 sK1 X0]
  have l29 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0 X0]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l29 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation4512_54173_implies_Equation54174 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation54174 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54173 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l2 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (sK0 ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 ((sK1 ◇ sK0) ◇ X0) X1]
  have l3 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l3 sK0 sK1 X1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54173_implies_Equation54172 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation54172 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54173 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54173_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation54175 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54173 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [l5 sK1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l8 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l5 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54173 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h54173 sK0 X0 (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ (X0 ◇ X0)) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1)) := by
    intro sK0 X0 X1 sK1
    conv => enter [1, 1]; rw [h54173 sK0 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l14 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) = ((sK0 ◇ (X0 ◇ X0)) ◇ X1) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X1]
    conv => enter [1]; rw [← l13 sK0 X0 X1 sK1]
  have l15 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) = (sK0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l14 sK0 X0 sK1 X1]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ X0) X1]
  have l16 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X1))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l15 sK0 X0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1, 2, 2]; rw [l11 sK0 sK1 X1]
    conv => enter [1]; rw [l16 sK0 X0 sK1 X1]
  have l18 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l12 sK0 X0 sK1]
    conv => enter [1]; rw [l17 sK0 X0 sK1 X1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l9 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54173 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

theorem Equation4512_54173_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54173 sK0 sK0 X0]
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

theorem Equation4512_54173_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54173 : Equation54173 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54173 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ X0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 sK0]
  intro x
  conv => enter [1]; rw [l7 x]

theorem Equation4512_53951_implies_Equation53934 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53951 : Equation53951 G) : Equation53934 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h53951 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53951 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l0 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation53951_implies_Equation53907 (G : Type*) [Magma G] (h53951 : Equation53951 G) : Equation53907 G := by
  intro x y
  conv => enter [1]; rw [h53951 x y y]

theorem Equation4512_53951_implies_Equation53897 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53951 : Equation53951 G) : Equation53897 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53951 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53951 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation53951_implies_Equation53870 (G : Type*) [Magma G] (h53951 : Equation53951 G) : Equation53870 G := by
  intro x y
  conv => enter [1]; rw [h53951 x y x]

theorem Equation4512_53951_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53951 : Equation53951 G) : Equation53860 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53951 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53951 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h53951 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h53951 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53951 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_53951_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53951 : Equation53951 G) : Equation53822 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53951 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53951_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53951 : Equation53951 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53951 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  intro x
  conv => enter [1]; rw [l1 x x]

theorem Equation4512_54261_implies_Equation54236 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54236 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54261 X2 X1 X1]
    conv => enter [1, 2]; rw [h54261 X1 X1 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [h4512 X2 (X1 ◇ X1) X3]
    conv => enter [1, 1]; rw [h54261 X2 X1 X0]
  have l3 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
  have l4 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l3 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l5 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l4 X2 X1 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l7 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l8 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l9 X0 X1 X3 X2]
  have l11 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X2 X1]
    conv => enter [1]; rw [l6 X2 X1 X2 X0]
  intro x y z
  conv => enter [1]; rw [l11 x y x x]
  conv => enter [1]; rw [l10 x x y z]

theorem Equation4512_54261_implies_Equation54190 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54190 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  have l6 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X2]
    conv => enter [1, 2]; rw [h54261 X2 X1 X0]
  intro x y z
  conv => enter [1]; rw [l6 x y x z]
  conv => enter [1, 2]; rw [h4512 z y (z ◇ y)]
  conv => enter [1]; rw [h54261 x (z ◇ y) z]
  conv => enter [1]; rw [h4512 z (z ◇ y) (z ◇ (z ◇ y))]
  conv => enter [1]; rw [l5 (z ◇ (z ◇ y)) z y x]

theorem Equation4512_54261_implies_Equation4272 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation4272 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l1 x x y]

theorem Equation4512_54261_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54186 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54261 X0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_54261_implies_Equation54240 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54240 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54261 X0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54261 X0 sK1 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54261 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l6 X0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1 sK0]
  have l8 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [h54261 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK1 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [l7 (sK1 ◇ sK1) sK1 sK0]
  have l10 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1, 2]; rw [← l1 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [← l8 X1 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l10 X0 sK0 sK1 sK0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_54261_implies_Equation54162 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54162 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l1 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [h4512 X2 (X1 ◇ X1) X3]
    conv => enter [1, 1]; rw [h54261 X2 X1 X0]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l1 X2 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
  have l3 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l4 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l3 X2 X1 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l4 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  intro x y
  conv => enter [1]; rw [l0 x y (y ◇ y)]
  conv => enter [1]; rw [← h4512 y y (y ◇ y)]
  conv => enter [1, 2]; rw [h54261 y y x]
  conv => enter [1]; rw [l5 y x y x]

theorem Equation4512_54261_implies_Equation54199 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54199 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54261 X2 X1 X1]
    conv => enter [1, 2]; rw [h54261 X1 X1 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l2 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [h4512 X2 (X1 ◇ X1) X3]
    conv => enter [1, 1]; rw [h54261 X2 X1 X0]
  have l3 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
  have l4 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l3 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l5 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l4 X2 X1 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l6 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l5 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l7 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l8 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
  have l10 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l9 X0 X1 X3 X2]
  have l11 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X2 X1]
    conv => enter [1]; rw [l6 X2 X1 X2 X0]
  intro x y
  conv => enter [1]; rw [l11 x y x x]
  conv => enter [1]; rw [l10 x x y y]

theorem Equation4512_54261_implies_Equation54202 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54202 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54261 X0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54261 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l5 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l6 X0 sK0]
  have l8 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54261 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1, 2]; rw [← l2 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l8 X1 sK0 X0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l10 X0 sK1 sK0 sK1]
  have l12 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l12 x y y]

theorem Equation4512_54261_implies_Equation54165 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54165 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54261 X0 (sK1 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54261 X0 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54261 X0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l6 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l5 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [← l6 X0 sK1]
  have l8 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [h54261 X1 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1 X0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
  have l11 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [l8 X1 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l2 (sK1 ◇ sK1) sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l11 sK0 sK1 X0 sK0]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l15 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 X0]
  have l16 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l15 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y x]

theorem Equation4512_54261_implies_Equation54172 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54172 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54261 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 x y x]

theorem Equation4512_54261_implies_Equation54175 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation54175 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54261 X0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_54261_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53850 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  have l6 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X2]
    conv => enter [1, 2]; rw [h54261 X2 X1 X0]
  intro x y z
  conv => enter [1]; rw [l6 x x x z]
  conv => enter [1, 2]; rw [h4512 z x (z ◇ x)]
  conv => enter [1]; rw [h54261 x (z ◇ x) z]
  conv => enter [1]; rw [h4512 z (z ◇ x) (z ◇ (z ◇ x))]
  conv => enter [1]; rw [l5 (z ◇ (z ◇ x)) z x y]

theorem Equation4512_54261_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53825 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54261 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l0 X0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x x]

theorem Equation4512_54261_implies_Equation53842 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53842 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK0 X0 sK2]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_54261_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53812 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_54261_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53832 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0 sK1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54261_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53815 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ X1)]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  have l6 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l2 X2 X1 X3 X2]
    conv => enter [1, 2]; rw [h54261 X2 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x x x y]
  conv => enter [1, 2]; rw [h4512 y x (y ◇ x)]
  conv => enter [1]; rw [h54261 x (y ◇ x) y]
  conv => enter [1]; rw [h4512 y (y ◇ x) (y ◇ (y ◇ x))]
  conv => enter [1]; rw [l5 (y ◇ (y ◇ x)) y x x]

theorem Equation4512_54261_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53835 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X3 ◇ (X1 ◇ X1)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54261 X0 X1 X0]
    conv => enter [1]; rw [← h54261 X3 X1 X0]
  have l1 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X1 ◇ X1)))) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [← h54261 X3 (X1 ◇ X1) X2]
    conv => enter [1, 2]; rw [h54261 (X1 ◇ X1) X1 X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X1)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54261 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X1 ◇ ((X2 ◇ X3) ◇ X1))]
  have l3 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [h4512 X2 (X1 ◇ X1) X3]
    conv => enter [1, 1]; rw [h54261 X2 X1 X0]
  have l4 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l3 X2 X1 X3 X0]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X3 X1]
  have l6 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1))))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l1 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 (X2 ◇ (X1 ◇ X1))]
  have l7 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l4 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l8 : ∀ X2 X1 X3 X0 : G, (X2 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [l7 X2 X1 X3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))) = (X2 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l8 X2 X1 X3 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l10 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [l0 X0 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X3 (X1 ◇ X1) X2]
    conv => enter [1, 2]; rw [l0 (X1 ◇ X1) X1 X0]
  have l11 : ∀ X3 X2 X1 X0 : G, (X3 ◇ (X2 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) := by
    intro X3 X2 X1 X0
    conv => enter [1]; rw [l5 X3 X2 X1 X2]
    conv => enter [1, 2, 2]; rw [l10 X2 X1 X2 X0]
  intro x y
  conv => enter [1]; rw [l11 x x x x]
  conv => enter [1]; rw [← l6 x y x x]
  conv => enter [1]; rw [l9 x y x y]

theorem Equation4512_54261_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53822 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l0 sK0 X1]
  have l2 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l2 X0 sK0 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK0]
  have l4 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation4512_54261_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54261 : Equation54261 G) : Equation53807 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54261 X0 sK0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK0 X0]
  intro x
  conv => enter [1]; rw [← l1 x x]

theorem Equation4512_53881_implies_Equation53874 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53874 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK2) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ (X1 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h53881 sK0 ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
  have l5 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← h53881 sK0 (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK2]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53881 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53881 X0 X1 X0]
    conv => enter [1]; rw [← h53881 X0 X2 X0]
  have l8 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53881 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2))]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h53881 (sK0 ◇ sK1) X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK2))]
  have l10 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK1) ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h53881 (sK0 ◇ sK1) X0 sK2]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 ((sK0 ◇ sK1) ◇ sK2)]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK1 X0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ sK2)]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 X0 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 sK0 sK2]
  have l16 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l8 sK1 ((sK1 ◇ sK2) ◇ X0) sK2]
  have l17 : ∀ sK1 X0 X1 sK2 : G, (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK1 X0 X1 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [l8 sK1 X0 sK2]
  have l18 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) = (sK1 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X1]
    conv => enter [1]; rw [← l17 sK1 X0 X1 sK2]
  have l19 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) = (sK1 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l18 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l20 : ∀ sK1 sK0 sK2 X1 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK0 sK2 X1
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ X1) sK0]
    conv => enter [1]; rw [← l19 sK1 sK2 X1 sK1]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l8 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK2]
    conv => enter [1]; rw [← l8 sK1 (sK1 ◇ sK2) sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l8 sK1 (sK1 ◇ sK2) sK2]
  have l24 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l8 sK1 (sK1 ◇ sK2) sK2]
  have l25 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l24 sK1 sK2 X0]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l25 sK1 sK2 X0]
    conv => enter [1]; rw [← l20 sK1 sK0 sK2 X0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l29 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l27 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l16 sK1 sK2 sK1]
  have l30 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l29 sK1 sK0 sK2]
    conv => enter [1]; rw [← l8 sK1 (sK1 ◇ sK2) sK2]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l30 sK1 sK0 sK2]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l33 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 sK1 sK0 sK2]
  have l35 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0]
  have l37 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0]
  have l38 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X0]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [l38 sK0 sK1 sK2 X0]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l8 sK1 sK2 sK2]
  have l41 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l39 sK0 sK1 sK2 X0]
  have l42 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l41 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
  have l43 : ∀ sK0 sK1 sK2 X1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l39 sK0 sK1 sK2 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 X1 sK0]
  have l44 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2]
  have l45 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53881 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l43 sK0 sK1 sK2 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1]; rw [l45 sK0 sK0 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l47 x y z]

theorem Equation4512_53881_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53888 G := by
  have l0 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h53881 sK2 X0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
  have l2 : ∀ sK2 X0 X1 sK1 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = (((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X1) := by
    intro sK2 X0 X1 sK1
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [l1 sK2 X0 sK1]
  have l3 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1)) = (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1)) X1]
    conv => enter [1]; rw [← l2 sK2 X0 X1 sK1]
  have l4 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1)) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l5 : ∀ sK2 sK1 X1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [l4 sK2 sK1 X1 sK2]
    conv => enter [1]; rw [l1 sK2 (sK2 ◇ X1) sK1]
  have l6 : ∀ sK2 sK1 X1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [l5 sK2 sK1 X1]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ sK1) sK1]
  have l7 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l1 sK2 sK1 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l8 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l7 sK2 sK1 X0]
    conv => enter [1]; rw [l6 sK2 sK1 X0]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ sK1) sK1]
  have l10 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [l8 sK2 sK1 X0]
  have l11 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [← l10 sK0 sK2 sK1 X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l11 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_53881_implies_Equation4268 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation4268 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1) sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

theorem Equation4512_53881_implies_Equation53864 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53864 G := by
  have l0 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ sK2) sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53881_implies_Equation53866 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53866 G := by
  have l0 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK2 ◇ sK1) sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53881_implies_Equation53873 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53873 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
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
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53881 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 sK1]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53881 (sK1 ◇ sK1) X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l4 sK1 (sK1 ◇ sK1)]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53881 X0 X1 X0]
    conv => enter [1]; rw [← h53881 X0 X2 X0]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53881 (sK1 ◇ (sK1 ◇ sK1)) X0 sK1]
    conv => enter [1]; rw [← l9 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l5 sK1]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0]
    conv => enter [1]; rw [← l2 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 X0]
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53881 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1, 2]; rw [← l9 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l18 sK1 X0]
    conv => enter [1, 2]; rw [l7 sK1]
  have l23 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1 X0]
    conv => enter [1]; rw [l11 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l25 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← l19 sK1 sK1]
    conv => enter [1]; rw [l24 sK1 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l27 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l14 sK0 ((sK0 ◇ sK1) ◇ X0) X1]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  have l29 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l20 sK1 sK1]
    conv => enter [1]; rw [← l20 sK1 (sK1 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l31 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l20 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l32 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l31 sK1 X0]
    conv => enter [1]; rw [l23 sK1 X0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l34 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l32 sK1 X0]
    conv => enter [1]; rw [← l25 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l36 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l20 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l34 sK1 X0]
  have l37 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l36 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l38 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l29 sK1]
    conv => enter [1]; rw [l37 sK1 X0]
  have l39 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l29 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l40 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l38 sK1 X0]
    conv => enter [1]; rw [← l39 sK1 X0]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l40 sK1 X0]
  have l43 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 X0]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1 sK1]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y
  conv => enter [1]; rw [l46 x y]

theorem Equation4512_53881_implies_Equation53872 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53872 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h53881 sK1 X0 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h53881 sK0 X0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53881 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK0 X0]
    conv => enter [1]; rw [← l5 sK1 sK0 X0]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [l1 sK1 sK0 (sK1 ◇ sK0)]
  have l11 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l10 sK1 sK0 X0]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l11 sK1 sK0 X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation4512_53881_implies_Equation53862 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53862 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← h53881 sK0 X0 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53881_implies_Equation53863 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53863 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53881_implies_Equation53870 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53870 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53881 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y y]

theorem Equation4512_53881_implies_Equation53860 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53860 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_53881_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53881 : Equation53881 G) : Equation53817 G := by
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
  have l11 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ X1)) = (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h53881 sK0 X1 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h53881 (sK0 ◇ sK0) X1 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53881 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53881 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53881 X0 X1 X0]
    conv => enter [1]; rw [← h53881 X0 X2 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53881 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53881 sK0 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53881 (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
    conv => enter [1]; rw [← l8 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l26 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l4 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← l23 sK0 X1 X0]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
    conv => enter [1]; rw [← l25 sK0 X1 X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l22 sK0 sK0]
    conv => enter [1]; rw [← l29 sK0 X0 sK0]
  have l34 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 X0 sK0]
    conv => enter [1]; rw [l17 sK0 sK0 sK1 sK2]
  have l35 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l22 sK0 sK0]
    conv => enter [1]; rw [l32 sK0 sK0]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK0]
    conv => enter [1]; rw [l34 sK0 sK0 sK1 sK2]
  have l37 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 1]; rw [← l36 sK0 sK1 sK2]
  have l38 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l37 sK0 sK1 sK2 X0]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l31 sK0 X0]
    conv => enter [1]; rw [l38 sK0 X0 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l35 sK0]
    conv => enter [1]; rw [l39 sK0 sK1 sK2 X0]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l24 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l42 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l24 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l41 sK0 X0]
  have l43 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 sK0]
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53881 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l43 sK0]
  have l45 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l44 sK0 X0]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l27 sK0 sK0]
    conv => enter [1]; rw [l45 sK0 sK0 sK1 sK2]
  have l47 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0]
    conv => enter [1]; rw [l46 sK0 sK1 sK2]
  have l48 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l15 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← l36 sK0 sK1 sK2]
  have l49 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l24 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l48 sK0 sK1 sK2 X0]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l49 sK0 sK1 sK2 sK0]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l47 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 sK2]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l54 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l55 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l15 sK1 sK1 sK2]
  have l56 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l55 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l57 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l54 sK1 sK2 X0]
    conv => enter [1]; rw [← l56 sK1 sK2 X0]
  have l58 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l57 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l59 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← l58 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y z
  conv => enter [1]; rw [l59 x y z]

end Semigroup5
