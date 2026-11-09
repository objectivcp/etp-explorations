import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54133_implies_Equation54047 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54047 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l1 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = (((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1, 1]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) (sK1 ◇ sK0) X0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l14 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l16 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54133 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK0]
  have l18 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← h54133 (sK1 ◇ (sK0 ◇ sK0)) sK0 X0 X1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l19 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l18 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l17 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l21 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l24 : ∀ sK0 X2 X3 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X2 ◇ (X3 ◇ X3)) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X2 X3 X0 X1
    conv => enter [1]; rw [← l22 (X2 ◇ (X3 ◇ X3)) X2 sK0]
    conv => enter [1, 2]; rw [← h54133 X0 X1 X2 X3]
  have l25 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X0 ◇ X1) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l22 (X0 ◇ X1) X1 sK0]
    conv => enter [1, 2]; rw [l22 X1 X0 sK0]
  have l26 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l22 X2 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK1 ◇ sK0) ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l22 ((sK1 ◇ sK0) ◇ X0) (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 2]; rw [l11 sK1 sK0]
  have l30 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54133 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l22 X0 X0 sK0]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 sK0 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ sK0) sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l22 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l34 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← l22 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l37 : ∀ X1 X2 X0 sK1 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro X1 X2 X0 sK1 sK0
    conv => enter [1]; rw [l30 X1 X2 X0 sK0]
    conv => enter [1, 2]; rw [l33 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) X0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))]
  have l41 : ∀ X2 X0 X1 sK1 sK0 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro X2 X0 X1 sK1 sK0
    conv => enter [1]; rw [← l26 sK0 X2 X0 X1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l42 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l43 : ∀ sK0 X2 X3 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((X3 ◇ X3) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X2 X3 X0 X1
    conv => enter [1]; rw [l24 sK0 X2 X3 X0 X1]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ X3) (X0 ◇ (X1 ◇ X0))]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l46 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l22 sK0 sK0 sK0]
    conv => enter [1]; rw [l37 sK0 sK0 X0 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l38 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l48 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l49 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1 X0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK0 sK0]
  have l51 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l33 sK0 sK1]
  have l52 : ∀ sK0 X2 X3 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro sK0 X2 X3 X0 X1
    conv => enter [1]; rw [l43 sK0 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X3 X3 (X0 ◇ (X1 ◇ X0))]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l46 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l44 sK0 sK0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l47 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l48 sK1 sK0]
  have l56 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [l41 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l57 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l44 sK0 sK0]
    conv => enter [1]; rw [l51 sK0 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l44 sK0 sK0]
  have l58 : ∀ sK0 X2 X3 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ (X3 ◇ (X3 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X2 X3
    conv => enter [1]; rw [l52 sK0 X2 X3 sK0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l22 sK0 sK0 sK0]
  have l59 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1, 1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l53 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l50 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1, 2]; rw [← l50 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1]
  have l62 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l56 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 sK1]
  have l63 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l57 sK0 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l50 sK0 sK1]
  have l64 : ∀ sK0 X2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 sK1
    conv => enter [1]; rw [l58 sK0 X2 sK0]
    conv => enter [1, 2]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l62 sK1 sK0]
  have l66 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l59 sK0 sK1 sK0]
  have l67 : ∀ sK0 X2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X2 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X2 sK1
    conv => enter [1]; rw [l64 sK0 X2 sK1]
    conv => enter [1, 2]; rw [← l34 sK1 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l65 sK0 sK1]
  have l69 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l66 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l60 sK0 sK1]
  have l70 : ∀ sK1 sK0 X2 : G, ((sK1 ◇ sK0) ◇ sK1) = (X2 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [← l33 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 X2 sK1]
    conv => enter [1, 2, 2]; rw [l33 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l68 sK0 sK1]
  have l72 : ∀ sK1 sK0 X2 : G, ((sK1 ◇ sK0) ◇ sK1) = (X2 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l70 sK1 sK0 X2]
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK1]
  have l73 : ∀ sK1 sK0 X2 : G, ((sK1 ◇ sK0) ◇ sK1) = (X2 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l72 sK1 sK0 X2]
    conv => enter [1, 2]; rw [l16 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l74 : ∀ sK1 sK0 X2 : G, ((sK1 ◇ sK0) ◇ sK1) = (X2 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X2
    conv => enter [1]; rw [l73 sK1 sK0 X2]
    conv => enter [1, 2]; rw [← l71 sK0 sK1]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1 sK0]
    conv => enter [1]; rw [← l74 sK1 sK0 sK0]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l75 sK0 sK1]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [l76 sK0 sK1]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1, 2]; rw [← l50 sK0 sK1]
  have l80 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1]; rw [← l61 sK0 sK1]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l80 sK1 sK0]
  have l82 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1, 2]; rw [l50 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l82 x y]

theorem Equation4512_54133_implies_Equation54011 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54011 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l10 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l11 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l12 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l11 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l13 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l10 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l14 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l9 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l12 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK0 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ sK1) sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l13 (sK0 ◇ sK1) sK0 sK0 sK1]
  have l21 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l13 X0 X1 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l13 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l25 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X2)) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l21 X0 X1 X2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X2]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l13 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l13 (sK0 ◇ sK1) sK0 sK0 sK1]
  have l29 : ∀ sK0 sK1 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [← l25 X0 X1 X2 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l13 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK0))]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l13 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK1) sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK1 X0]
    conv => enter [1]; rw [← l39 sK0 sK1 X0]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l40 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l42 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1]
  have l46 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h54133 X1 X2 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l13 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l46 sK0 sK0 X0 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK1 X0]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l48 sK0 sK1 X0]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1 X0]
  have l51 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l50 sK0 sK1 sK0]
    conv => enter [1]; rw [← l46 X1 X2 sK0 sK0 sK1]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1 X0]
    conv => enter [1]; rw [l18 sK0 sK1 X0]
  have l54 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l53 sK0 sK1 X0]
  have l55 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [l54 sK0 sK1 X0]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l13 (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l50 sK0 sK1 X0]
  have l57 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l56 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l58 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l57 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l37 sK0 sK1]
  have l59 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l58 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l38 sK0 sK1]
  have l60 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1 X0]
  have l61 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l60 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
  have l62 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l51 sK0 sK1 (sK0 ◇ X0) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l3 sK0 sK1 X0]
  have l63 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l62 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))]
  have l64 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l63 sK0 sK1 X0]
    conv => enter [1]; rw [← l29 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) sK0 X0]
  have l65 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l64 sK0 sK1 X0]
    conv => enter [1]; rw [← l33 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l66 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l65 sK0 sK1 X0]
    conv => enter [1]; rw [← l61 sK0 sK1 X0 (sK0 ◇ (sK1 ◇ sK0))]
  have l67 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l14 X0 X1 sK0 sK1]
  have l68 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X2)) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l67 X0 X1 X2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X2]
  have l69 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [l68 X0 X1 X2 sK0 sK1]
    conv => enter [1]; rw [← l55 sK0 sK1 X2]
  have l70 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l66 sK0 sK1 X2]
    conv => enter [1]; rw [← l69 X0 X1 X2 sK0 sK1]
  have l71 : ∀ sK0 sK1 X0 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l70 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  intro x y
  conv => enter [1]; rw [l71 x y x x y]

theorem Equation4512_54133_implies_Equation54048 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54048 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y
  conv => enter [1]; rw [l1 x y y x x]

theorem Equation4512_54133_implies_Equation54024 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54024 G := by
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
  have l3 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54133 X0 X1 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK1]
  have l4 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l3 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l2 sK1]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l4 X0 X1 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((X0 ◇ X1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1) X1 sK1]
    conv => enter [1, 2]; rw [l5 X1 X0 sK1]
  have l7 : ∀ sK1 X2 X3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((X2 ◇ X3) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro sK1 X2 X3 X0 X1
    conv => enter [1]; rw [← l5 (X2 ◇ X3) X3 sK1]
    conv => enter [1, 2]; rw [h54133 X3 X2 X0 X1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK1) sK1]
  have l9 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK1]
  have l10 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK1) sK1]
  have l11 : ∀ X1 X2 X0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X1 X2 X0 sK1
    conv => enter [1]; rw [h54133 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [l5 X0 X0 sK1]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
    conv => enter [1]; rw [h54133 sK1 sK1 X0 X1]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l14 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [← l12 sK1 X0 X1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l15 : ∀ X1 X2 X0 sK1 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro X1 X2 X0 sK1 sK0
    conv => enter [1]; rw [l11 X1 X2 X0 sK1]
    conv => enter [1, 2]; rw [l13 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [l13 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 sK1]
    conv => enter [1]; rw [← l8 sK1]
  have l19 : ∀ sK1 X2 X3 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) := by
    intro sK1 X2 X3 X0 X1
    conv => enter [1]; rw [l7 sK1 X2 X3 X0 X1]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l20 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l6 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l21 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
    conv => enter [1]; rw [l15 sK1 sK1 X0 sK1 sK0]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l17 sK1 sK0]
  have l24 : ∀ sK1 X2 X3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (X3 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 X2 X3 sK0
    conv => enter [1]; rw [l19 sK1 X2 X3 sK1 sK1]
    conv => enter [1, 2, 2]; rw [l14 sK1 sK1 sK1 sK0]
  have l25 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l13 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [l13 sK1 sK0]
  have l26 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l13 sK1 sK0]
    conv => enter [1]; rw [l21 sK1 X0 sK0]
  have l27 : ∀ sK1 X2 X3 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (X3 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l24 sK1 X2 X3 sK1]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK1]
  have l28 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l22 sK1 sK1]
    conv => enter [1]; rw [l25 sK1 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK1]
  have l29 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l22 sK1 sK1]
    conv => enter [1]; rw [l26 sK1 sK1 X0]
    conv => enter [1, 2]; rw [← l22 sK1 sK1]
  have l30 : ∀ sK1 X2 X3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X2 X3 sK0
    conv => enter [1]; rw [l27 sK1 X2 X3]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK1]
  have l31 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l28 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK1]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l29 sK1 X0]
    conv => enter [1, 2]; rw [← l18 sK0 sK1]
  have l33 : ∀ sK1 sK0 X2 X3 : G, ((sK1 ◇ sK0) ◇ sK1) = (X2 ◇ (X3 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X2 X3
    conv => enter [1]; rw [← l13 sK1 sK0]
    conv => enter [1]; rw [l30 sK1 X2 X3 sK0]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← l33 sK1 sK0 sK0 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l23 sK1 sK0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [l35 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l36 x y]

theorem Equation4512_54133_implies_Equation54060 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54060 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ ((X3 ◇ X2) ◇ X4)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X4) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [h4512 X2 (X3 ◇ X2) X4]
    conv => enter [1, 1]; rw [h54133 X2 X3 X0 X1]
  have l1 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X4)) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [l0 X2 X3 X4 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X4]
  have l2 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X4))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X4]
  have l3 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ ((X3 ◇ X2) ◇ X4)) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X4)))) := by
    intro X2 X3 X4 X0 X1
    conv => enter [1]; rw [l2 X2 X3 X4 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X4]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X4)))) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l3 X2 X3 X4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  intro x y
  conv => enter [1]; rw [h54133 x y (x ◇ x) (x ◇ x)]
  conv => enter [1, 2]; rw [← h54133 x x (x ◇ x) x]
  conv => enter [1]; rw [← h4512 x x (x ◇ (x ◇ x))]
  conv => enter [1]; rw [l4 x x x y y]

theorem Equation4512_54133_implies_Equation54014 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54014 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l2 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l1 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [h54133 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54133 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [← l3 sK1 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l5 sK1 sK0]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [← h54133 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK1) X0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54133 sK1 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l15 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l14 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54133 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l16 x y]

theorem Equation4512_54133_implies_Equation54057 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54057 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 X0 X1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 y x x y]

theorem Equation4512_54133_implies_Equation54021 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54021 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l2 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation4512_54133_implies_Equation54050 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54050 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l2 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54133_implies_Equation54020 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54020 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54133 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l2 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK0) sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54133_implies_Equation54013 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54013 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54133_implies_Equation54023 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation54023 G := by
  have l0 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54133 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l1 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK0]
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 (sK1 ◇ sK0) sK0 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK1 sK1 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 sK0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l18 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h54133 X1 X2 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK1 sK1 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK1 X0 sK0 sK1]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l3 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0 X0]
  have l21 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 sK0 X0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l21 sK1 sK0 X0]
  have l23 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l22 sK0 sK1 sK0]
    conv => enter [1]; rw [← l18 X1 X2 sK0 sK0 sK1]
  have l24 : ∀ sK0 sK1 X2 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 sK1 X2 X0 X1
    conv => enter [1]; rw [l23 sK0 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y
  conv => enter [1]; rw [l24 x y x y y]

theorem Equation4512_54133_implies_Equation53827 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53827 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l24 sK0 X0 X1]
  have l26 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l22 sK0 X2]
    conv => enter [1]; rw [← l25 X0 X1 X2 sK0]
  have l27 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l26 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l28 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l27 sK0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l28 x y x z]

theorem Equation4512_54133_implies_Equation53844 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53844 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l9 sK0 sK2 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l18 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l22 sK2 sK0 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l24 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ X0 X1 X2 sK2 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK2 sK0
    conv => enter [1]; rw [← h54133 X2 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l24 sK2 sK0 X2]
  have l27 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l24 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [h54133 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0 X1]
  have l28 : ∀ sK2 sK0 X2 : G, (sK2 ◇ (sK0 ◇ sK2)) = (X2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X2
    conv => enter [1]; rw [l27 sK2 sK0 sK2 sK2]
    conv => enter [1]; rw [l26 sK2 sK2 X2 sK2 sK0]
  have l29 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l28 sK0 sK0 X2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2]; rw [l25 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

theorem Equation4512_54133_implies_Equation53814 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53814 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [l15 X0 X1 X2 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [l17 (sK0 ◇ sK0) X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l17 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0 sK0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l24 sK0 X0 X1]
  have l26 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l22 sK0 X2]
    conv => enter [1]; rw [← l25 X0 X1 X2 sK0]
  have l27 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1, 2]; rw [h4512 X1 X0 X2]
    conv => enter [1]; rw [← l26 sK0 X0 X1 X2]
  have l28 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l27 X0 X1 X2 sK0]
    conv => enter [1]; rw [← l23 sK0]
  intro x y z
  conv => enter [1]; rw [← l28 x y z x]

theorem Equation4512_54133_implies_Equation53819 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53819 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0]
  have l18 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l17 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l24 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l25 sK1 sK2 X0 sK0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l24 sK1 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 X0 X1 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK0 X0 X1 sK1 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 1]; rw [← l24 sK1 sK2 sK0 X0]
  have l29 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X1]
    conv => enter [1]; rw [← l28 sK0 X0 X1 sK1 sK2]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l29 sK0 sK1 sK2 sK1 sK1]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l31 x y z]

theorem Equation4512_54133_implies_Equation53828 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53828 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l5 sK0 sK0 sK2]
    conv => enter [1]; rw [← l6 sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 (sK0 ◇ sK0) X0 sK0]
  have l11 : ∀ X2 X3 X1 X0 sK0 : G, (X2 ◇ (X3 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 X1 X0 sK0
    conv => enter [1]; rw [h54133 X2 X3 X1 X1]
    conv => enter [1, 2]; rw [h54133 X1 X1 X0 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 sK0 X0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l5 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 X1 X0 sK0]
  have l15 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK2 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l9 sK0 sK2]
    conv => enter [1]; rw [l10 sK0 X0]
  have l16 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l14 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l17 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK2 sK0]
  have l18 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l16 sK0 X1]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [l17 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4512_54133_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53846 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l24 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l25 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l24 sK0 X0 X1]
  have l26 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← l22 sK0 X2]
    conv => enter [1]; rw [← l25 X0 X1 X2 sK0]
  have l27 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l26 sK0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l28 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l27 sK0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l28 x y z x]

theorem Equation4512_54133_implies_Equation53855 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53855 G := by
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
  have l3 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [← h54133 X0 X1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l2 sK1]
    conv => enter [1]; rw [l3 sK1 X0 X1]
  have l5 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l4 sK1 X0 X1]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [← l6 sK1]
  have l10 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [← h54133 X0 X1 sK1 sK1]
  have l11 : ∀ sK1 X2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X2 X0 X1
    conv => enter [1]; rw [l10 sK1 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l11 x y z w]

theorem Equation4512_54133_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53818 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l11 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l10 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l11 x x y z]

theorem Equation4512_54133_implies_Equation53848 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53848 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l9 sK0 sK2 sK1]
    conv => enter [1]; rw [← l10 sK0]
  have l18 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l17 sK2 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l22 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l24 sK2 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ X0 X1 X2 sK2 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK2 sK1
    conv => enter [1]; rw [← h54133 X2 (X0 ◇ (X0 ◇ X0)) X0 X1]
    conv => enter [1, 2]; rw [← l24 sK2 sK1 X0 X2]
  have l27 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l24 sK2 sK1 sK2 (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))]
    conv => enter [1]; rw [h54133 (sK2 ◇ (sK2 ◇ sK2)) sK2 X0 X1]
  have l28 : ∀ sK2 sK1 X2 : G, (sK2 ◇ (sK1 ◇ sK2)) = (X2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X2
    conv => enter [1]; rw [l27 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [l26 sK2 sK2 X2 sK2 sK1]
  have l29 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l28 sK0 sK0 X2]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2]; rw [l25 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l30 x y z]

theorem Equation4512_54133_implies_Equation53813 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53813 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l15 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l18 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK0 X0]
    conv => enter [1]; rw [← l23 sK0 X0]
  have l25 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l24 sK1 sK0 X0]
    conv => enter [1]; rw [← l25 sK1 sK0 X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 1]; rw [← l24 sK1 sK0 X0]
  have l29 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l26 sK0 sK1 X1]
    conv => enter [1]; rw [← l28 sK0 X0 X1 sK1]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l29 sK0 sK1 sK1 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation4512_54133_implies_Equation53825 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53825 G := by
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
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54133 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 (sK0 ◇ X0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l11 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [l8 X0 X1 sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0]
  have l14 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l11 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK0) sK0 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) sK0 sK0]
  have l19 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l14 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← l24 sK0 X0]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2]; rw [← l18 sK0]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l28 sK1 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l25 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l33 x y]
  conv => enter [1]; rw [l32 x y]

theorem Equation4512_54133_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53826 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l4 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l6 sK0 X0]
  have l12 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 sK0 X0 X1]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0]
  have l16 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l12 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l18 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l16 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l23 : ∀ sK0 X0 sK1 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK0 X0]
  have l24 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l23 sK0 X0 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l24 sK0 X0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l27 : ∀ X2 X0 X1 X3 sK0 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X3 ◇ (X3 ◇ (sK0 ◇ sK0))) := by
    intro X2 X0 X1 X3 sK0
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h54133 X2 (X0 ◇ X1) X3 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h54133 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 sK0]
  have l29 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l27 X2 X0 X1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l29 x y x y]

theorem Equation4512_54133_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53833 G := by
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
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54133 X0 X1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l10 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 (sK0 ◇ sK0) X0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54133 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 sK0]
  have l16 : ∀ X2 X3 X1 X0 sK0 : G, (X2 ◇ (X3 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X2 X3 X1 X0 sK0
    conv => enter [1]; rw [h54133 X2 X3 X1 X1]
    conv => enter [1, 2]; rw [h54133 X1 X1 X0 sK0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 sK0 X0 sK0]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54133 sK1 (sK1 ◇ (sK0 ◇ sK1)) X0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  have l19 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h54133 X0 X1 sK0 sK0]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l10 sK0 sK0 sK1 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 X0]
  have l22 : ∀ X2 X3 X1 sK1 sK0 : G, (X2 ◇ (X3 ◇ X2)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro X2 X3 X1 sK1 sK0
    conv => enter [1]; rw [l16 X2 X3 X1 X2 sK0]
    conv => enter [1, 2]; rw [l18 X2 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 sK1]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54133 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54133 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l20 sK0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 sK0]
  have l27 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [← l10 sK1 sK1 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK1 X1 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l29 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l26 sK0]
  have l30 : ∀ sK0 X1 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l27 sK1 sK0 X1]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l5 sK0]
    conv => enter [1]; rw [l29 sK0]
  have l32 : ∀ sK0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1
    conv => enter [1]; rw [l30 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l31 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [← l32 sK0 sK0]
  have l35 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [l34 sK0]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l25 sK1 sK0]
  have l38 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l36 sK0 sK1]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [l39 sK0 sK1]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l38 sK1 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l42 sK0 sK1]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0]
    conv => enter [1]; rw [← l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l47 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l47 sK1 sK0 (sK0 ◇ sK1)]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [← l48 sK0 sK1]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK0 ◇ sK1))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l49 sK1 sK0]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [l51 sK1 sK0]
  have l53 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54133 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l52 sK1 sK0]
  have l54 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l50 sK1 sK0]
    conv => enter [1]; rw [← l53 X0 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l54 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l55 x y]

theorem Equation4512_54133_implies_Equation53840 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53840 G := by
  have l0 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h54133 X0 X1 sK1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l1 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK2)) (sK2 ◇ sK2)]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK1 sK2]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h54133 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [l4 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l5 y z x]

theorem Equation4512_54133_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53809 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← l7 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation4512_54133_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53812 G := by
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
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l11 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [l10 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y
  conv => enter [1]; rw [l11 x x y x]

theorem Equation4512_54133_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 sK0 X0 sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h54133 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54133_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53832 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h54133 X0 X1 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l5 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l2 sK0]
    conv => enter [1]; rw [l3 sK0 X0 X1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0) sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1 sK0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l15 sK0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l18 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54133 X1 X2 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l17 sK0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK1 sK1 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK1 X0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  have l23 : ∀ sK0 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X2 ◇ X1)) := by
    intro sK0 X1 X2
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l18 X1 X2 sK0 sK0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h54133 sK1 sK1 sK1 sK0]
    conv => enter [1]; rw [← l23 sK0 sK1 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l24 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation4512_54133_implies_Equation53823 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53823 G := by
  have l0 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h54133 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l0 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 (sK0 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_54133_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53815 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X3 X4 X2 X0 X1 : G, (X3 ◇ (X4 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X4 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X4 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  intro x y
  conv => enter [1]; rw [l1 x x x y y]

theorem Equation4512_54133_implies_Equation53836 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53836 G := by
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
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l4 sK0 X0 X1]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 sK0 X0 X1]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

theorem Equation4512_54133_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53816 G := by
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
  have l3 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l1 sK1 sK1]
    conv => enter [1]; rw [← h54133 X0 X1 (sK1 ◇ sK1) sK1]
  have l4 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l2 sK1]
    conv => enter [1]; rw [l3 sK1 X0 X1]
  have l5 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l4 sK1 X0 X1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
  have l8 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l9 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]

theorem Equation4512_54133_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53835 G := by
  have l0 : ∀ X0 X1 X4 X5 : G, (X0 ◇ (X1 ◇ X0)) = (X4 ◇ (X5 ◇ X4)) := by
    intro X0 X1 X4 X5
    conv => enter [1]; rw [h54133 X0 X1 X0 X0]
    conv => enter [1]; rw [← h54133 X4 X5 X0 X0]
  have l1 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X4) = (X2 ◇ ((X3 ◇ X2) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (X3 ◇ X2) X4]
  have l2 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X4) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X3 X2 X4]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ ((X1 ◇ X0) ◇ X4)) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X4]
    conv => enter [1]; rw [l2 X0 X1 X4 X2 X3]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X4))) = (X2 ◇ (X3 ◇ (X2 ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X0 X4]
    conv => enter [1]; rw [l3 X0 X1 X4 X2 X3]
  have l5 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ X3)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h54133 X3 X4 X2 X2]
    conv => enter [1]; rw [l4 X2 X2 X2 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x x x x x]
  conv => enter [1]; rw [l4 x x x y y]

theorem Equation4512_54133_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53808 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
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
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 (sK0 ◇ sK0) X0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54133 (sK0 ◇ sK0) (sK0 ◇ sK0) X0 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54133 sK0 sK0 X0 sK0]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h54133 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h54133 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 sK0]
  have l18 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← h54133 (X0 ◇ (sK0 ◇ sK0)) X0 X1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l19 : ∀ X1 sK0 X0 : G, (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l18 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [l14 sK0]
    conv => enter [1]; rw [← l19 X1 sK0 X0]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l21 X0 sK0 X0]
    conv => enter [1]; rw [l11 X0 sK0 sK1]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [← l22 X0 sK0 sK0]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l26 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l7 sK0 X0]
  have l28 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l17 sK0 X0 X1]
  have l29 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l28 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← l29 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) (sK0 ◇ sK0) X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l33 x y]

theorem Equation4512_54133_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53822 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 X0]
  have l10 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X2) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l7 sK0 X0 X1]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ ((X1 ◇ X0) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [l10 X0 X1 X2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X2]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← l7 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0]
  have l16 : ∀ sK0 X2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [← l13 X0 X1 X2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l24 : ∀ X0 X1 X2 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 X2 sK0
    conv => enter [1]; rw [← h54133 X2 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
    conv => enter [1, 2]; rw [← l23 sK0 X2]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [h54133 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0 X1]
  have l26 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X2
    conv => enter [1]; rw [l25 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK0 X2 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l21 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l27 x y]

theorem Equation4512_54133_implies_Equation53807 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54133 : Equation54133 G) : Equation53807 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
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
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54133 X0 X1 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l7 sK0 X0 X1]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X1 ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l11 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l12 sK0]
  intro x
  conv => enter [1]; rw [l14 x]

theorem Equation4512_54118_implies_Equation54053 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54118 : Equation54118 G) : Equation54053 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l0 sK1 sK0 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h54118 X1 X2 X1]
    conv => enter [1, 2]; rw [h54118 X1 X1 X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54118 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X3 ◇ X0)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54118 X0 X1 X0]
    conv => enter [1]; rw [← h54118 X0 X3 X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h54118 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 X0]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l6 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l10 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0 sK1]
  have l12 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l13 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) sK0]
  have l14 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [l6 sK0 sK2 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54118 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l6 sK0 sK0 sK2]
  have l16 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l6 sK0 sK2 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK2]
  have l17 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2, 1]; rw [l6 sK0 sK2 sK1]
  have l18 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1, 1]; rw [l12 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 sK0 X0 sK1]
  have l20 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l13 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l21 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l22 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l16 sK0 sK2]
    conv => enter [1]; rw [l6 (sK0 ◇ (sK2 ◇ sK0)) sK0 X0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK0]
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK0 X0]
    conv => enter [1, 1]; rw [l6 sK0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK0 sK1]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0 sK1]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [l24 sK1 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2, 2]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1]
  have l27 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l6 (sK0 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK0]
    conv => enter [1]; rw [l27 sK0 sK1 sK0 sK2]
  have l29 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0 X0]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l4 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l31 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 (sK1 ◇ sK0) X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l0 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l33 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l4 (sK1 ◇ sK0) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X1 ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))]
  have l34 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l33 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l35 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l32 sK1 sK0 X0]
    conv => enter [1]; rw [← l17 sK1 sK0 sK2 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))]
  have l36 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l31 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l14 sK1 sK0 sK2 sK0]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l8 sK1 sK0 sK1]
  have l38 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK0 sK0]
  have l39 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l35 sK1 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
  have l40 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l36 sK0 X0 sK1 sK0]
    conv => enter [1]; rw [← l28 sK0 sK1 sK0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 (sK1 ◇ sK0)]
  have l42 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l38 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l11 sK1 sK0]
  have l43 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l39 sK1 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l11 sK1 sK0]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l40 sK0 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK0 sK1]
  have l45 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l17 sK1 sK0 sK2 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l46 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l47 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l43 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l48 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l49 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l45 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l50 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l46 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l26 sK0 sK1 sK2]
  have l51 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l47 sK1 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l26 sK0 sK1 sK2]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1]; rw [l48 sK0 sK0 sK1]
  have l53 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2, 2]; rw [l6 sK0 sK2 sK1]
    conv => enter [1]; rw [l49 sK1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [l6 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l50 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l55 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l51 sK1 sK0 X0 sK2]
    conv => enter [1]; rw [← l29 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 X0 sK0]
  have l57 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l53 sK1 sK0 sK2]
    conv => enter [1]; rw [← l55 sK1 sK0 X0 sK2]
  have l58 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l56 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ (sK1 ◇ sK0))]
  have l59 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l57 sK1 sK0 sK2 sK1]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK1 sK0]
  have l60 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [l58 sK0 sK1 X0]
  have l61 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [← l59 sK1 sK0 sK2]
  have l62 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l63 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l25 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l64 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l62 sK1 sK0 sK2]
    conv => enter [1]; rw [← l17 sK1 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l65 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l61 sK1 sK0 sK2]
    conv => enter [1]; rw [l64 sK1 sK0 sK2]
  have l66 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 (sK1 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l60 sK0 sK1 (sK1 ◇ sK0)]
  have l67 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54118 (sK1 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l60 sK0 sK1 (sK1 ◇ sK0)]
  have l68 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l67 sK1 sK0 X0]
  have l69 : ∀ sK1 sK0 X0 sK2 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [l66 sK1 sK0 X0]
    conv => enter [1]; rw [← l63 sK1 sK0 sK2 (sK0 ◇ (sK1 ◇ sK0))]
  have l70 : ∀ sK1 sK0 sK2 X0 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l65 sK1 sK0 sK2]
    conv => enter [1]; rw [← l69 sK1 sK0 X0 sK2]
  have l71 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK1 sK0]
    conv => enter [1]; rw [← l70 sK1 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l71 x y z]

@[equational_result]
theorem Equation54118_implies_Equation4269 (G : Type*) [Magma G] (h54118 : Equation54118 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54118 sK0 sK0 sK0]
    conv => enter [1]; rw [← h54118 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4512_54118_implies_Equation54071 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54118 : Equation54118 G) : Equation54071 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X3 ◇ X0)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54118 X0 X1 X0]
    conv => enter [1]; rw [← h54118 X0 X3 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54118 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 ((X2 ◇ X3) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X3 (X0 ◇ X0)]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ X0)) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h54118 X0 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 (X0 ◇ X0) (X0 ◇ X0) X1]
  have l5 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ ((X2 ◇ X0) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l6 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X3) = (X0 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l5 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X0 X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← l4 X0 X2 X1]
  have l8 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ X3)) = (X0 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) X3]
    conv => enter [1]; rw [l6 X0 X1 X3 X2]
  have l9 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X3))) = (X0 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 X3]
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
  have l10 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X3 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l2 X0 X2 X3 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l3 (X0 ◇ X0) X1 X3 (X0 ◇ X0)]
  have l11 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ X0)) = (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X2 X3 X1
    conv => enter [1]; rw [l10 X0 X2 X3 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
  intro x y z
  conv => enter [1]; rw [l11 x y y x]
  conv => enter [1, 2]; rw [l7 x x x]
  conv => enter [1, 2]; rw [l3 x x x y]
  conv => enter [1, 2]; rw [h4512 x x (y ◇ x)]
  conv => enter [1]; rw [l9 y (x ◇ x) x z]

theorem Equation4512_54118_implies_Equation54026 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54118 : Equation54118 G) : Equation54026 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X3 ◇ X0)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54118 X0 X1 X0]
    conv => enter [1]; rw [← h54118 X0 X3 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X2 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← h54118 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h54118 sK0 sK0 X0]
  have l3 : ∀ sK0 sK1 X1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 X1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK0 X1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y y z]

theorem Equation4512_54118_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54118 : Equation54118 G) : Equation54034 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X3 ◇ X0)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54118 X0 X1 X0]
    conv => enter [1]; rw [← h54118 X0 X3 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z y]

end Semigroup5
