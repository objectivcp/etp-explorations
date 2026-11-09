import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation3316_4512_implies_Equation54023 (G : Type*) [Magma G] (h3316 : Equation3316 G) (h4512 : Equation4512 G) : Equation54023 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3316 sK1 sK0]
    conv => enter [1]; rw [h3316 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← h3316 sK1 sK0]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h3316 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l2 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) X0]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [h3316 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l5 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK0 X0]
    conv => enter [1]; rw [← l3 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h3316 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (X0 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3316 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3316 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l10 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3316 sK1 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l22 sK1 sK0]
    conv => enter [1]; rw [h3316 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l22 sK1 sK0]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 ((sK1 ◇ sK0) ◇ sK1)]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ sK1) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 X0]
  have l32 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l31 sK0 sK1 X0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l26 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 ((sK1 ◇ sK0) ◇ sK1)]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1 ((sK1 ◇ sK0) ◇ sK1)]
    conv => enter [1]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 X0]
  have l40 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l39 sK0 sK1 X0]
  have l41 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1, 2]; rw [h3316 sK1 sK0]
    conv => enter [1]; rw [l7 X0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← h3316 sK1 sK0]
  have l42 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l41 (sK0 ◇ (sK1 ◇ sK0)) sK1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l44 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 (sK1 ◇ sK0)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l46 x y]

theorem Equation3316_4512_54013_54023_implies_Equation41743 (G : Type*) [Magma G] (h3316 : Equation3316 G) (h4512 : Equation4512 G) (h54013 : Equation54013 G) (h54023 : Equation54023 G) : Equation41743 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h3316 sK0 sK1]
    conv => enter [1]; rw [h3316 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [h3316 sK0 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1, 2]; rw [← h3316 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3316 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [← l5 sK1 sK0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK1 ◇ (sK0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 sK0 X0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l10 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3316 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h54023 ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) sK0]
    conv => enter [1, 2, 2]; rw [← h3316 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [← h3316 sK0 sK1]
    conv => enter [1]; rw [h54023 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2, 2]; rw [h3316 sK0 sK1]
  have l12 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l13 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h3316 sK0 sK1]
    conv => enter [1, 1, 2]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1, 2, 1]; rw [← h3316 sK0 sK1]
  have l14 : ∀ sK1 sK0 : G, (((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l15 sK1 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [l20 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [h54013 sK0 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  have l28 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) sK0 X0]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1]; rw [l28 sK0 sK1 X0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l31 x y]

theorem Equation3316_4512_54020_implies_Equation41773 (G : Type*) [Magma G] (h3316 : Equation3316 G) (h4512 : Equation4512 G) (h54020 : Equation54020 G) : Equation41773 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54020 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation3316_4512_41534_implies_Equation41790 (G : Type*) [Magma G] (h3316 : Equation3316 G) (h4512 : Equation4512 G) (h41534 : Equation41534 G) : Equation41790 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3316 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h41534 (sK0 ◇ sK1) X0]
    conv => enter [1, 2, 2, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 sK1 (X0 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation307_3258_implies_Equation41534 (G : Type*) [Magma G] (h307 : Equation307 G) (h3258 : Equation3258 G) : Equation41534 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1, 2]; rw [h3258 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation307_3258_4512_implies_Equation54186 (G : Type*) [Magma G] (h307 : Equation307 G) (h3258 : Equation3258 G) (h4512 : Equation4512 G) : Equation54186 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h3258 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h3258 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h307 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  have l6 : ∀ sK1 X0 X1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l7 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l5 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
  have l8 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l7 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l6 sK1 X0 X0]
    conv => enter [1]; rw [← l3 X0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l10 : ∀ X0 sK2 sK1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1, 2]; rw [l8 sK2 sK1 X0 X0]
    conv => enter [1]; rw [← l3 X0 (sK1 ◇ sK1) (sK2 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l9 X0 sK1]
    conv => enter [1]; rw [← l10 X0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l11 x y z]

theorem Equation307_3255_4512_implies_Equation41534 (G : Type*) [Magma G] (h307 : Equation307 G) (h3255 : Equation3255 G) (h4512 : Equation4512 G) : Equation41534 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3255 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation307_3255_4512_53860_implies_Equation53866 (G : Type*) [Magma G] (h307 : Equation307 G) (h3255 : Equation3255 G) (h4512 : Equation4512 G) (h53860 : Equation53860 G) : Equation53866 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h3255 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3255 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h307 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3255 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h3255 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← h3255 (sK2 ◇ sK1) sK0]
  have l12 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h307 (sK2 ◇ sK1)]
  have l13 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l14 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l15 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))]
    conv => enter [1, 2]; rw [← h3255 (sK0 ◇ (sK2 ◇ sK1)) sK0]
  have l16 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l15 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1))]
  have l17 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h3255 sK1 sK2]
  have l18 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l17 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 sK1]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3255 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l6 sK0 sK1]
  have l22 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l13 sK0 sK2 sK1]
  have l23 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l22 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
  have l24 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3255 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l14 sK0 sK2 sK1]
  have l25 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h3255 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l16 sK0 sK2 sK1]
  have l26 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [h3255 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [l18 sK2 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1)]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l24 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))]
  have l30 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l29 sK0 sK2 sK1]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l26 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ sK1)]
  have l32 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1]; rw [l31 sK0 sK2 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← l8 sK0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l8 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l35 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l8 sK0 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) X0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l8 sK0 sK1 ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l37 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l35 sK0 sK2 sK1 X0]
  have l38 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l33 sK0 sK1 X0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l8 sK0 sK1 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [h3255 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l40 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [l34 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l44 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [l40 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 (sK0 ◇ sK1)]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l43 sK0 sK1]
    conv => enter [1, 2]; rw [l8 sK0 sK1 (sK0 ◇ sK1)]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK0 sK1]
  have l47 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [h53860 sK0 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK2 ◇ sK1) X0]
  have l48 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l47 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h3255 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l37 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l49 sK0 sK1 sK2]
    conv => enter [1]; rw [l36 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [← l48 sK0 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [l52 sK0 sK1 sK2]
  have l54 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l53 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1 sK1]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 sK1]
    conv => enter [1]; rw [l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l58 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l41 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [l8 sK0 sK1 (sK2 ◇ sK1)]
  have l59 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [l54 sK0 sK1 ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0) sK2]
    conv => enter [1, 2]; rw [← l37 sK0 sK2 sK1 X0]
  have l60 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l58 sK0 sK2 sK1]
    conv => enter [1]; rw [l54 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2]
    conv => enter [1, 2]; rw [← l58 sK0 sK2 sK1]
  have l61 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l59 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l25 sK0 sK2 sK1]
  have l62 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l60 sK0 sK2 sK1]
    conv => enter [1]; rw [← l61 sK0 sK2 sK1]
  have l63 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l0 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l30 sK0 sK2 sK1]
  have l64 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [l0 sK1 X0 X1]
    conv => enter [1]; rw [← l57 sK0 sK1 (sK1 ◇ (X0 ◇ (X1 ◇ sK1)))]
  have l65 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l64 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l57 sK0 sK1 (X0 ◇ (X1 ◇ sK1))]
  have l66 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l63 sK2 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l62 sK0 sK2 sK1]
  have l67 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l20 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1 X0 X1]
  have l68 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [l67 sK0 sK1 X0 X1]
  have l69 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l66 sK2 sK1 sK0]
  have l70 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l59 sK0 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l69 sK0 sK2 sK1]
  have l71 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l60 sK0 sK2 sK1]
    conv => enter [1]; rw [← l70 sK0 sK2 sK1]
  have l72 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l71 sK0 sK2 sK1]
    conv => enter [1]; rw [l23 sK0 sK2 sK1]
  have l73 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l68 sK0 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l32 sK0 sK2 sK1]
  have l74 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l73 sK0 sK1 sK2]
    conv => enter [1]; rw [← l37 sK0 sK2 sK1 (sK2 ◇ sK1)]
  have l75 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [← l72 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l75 x y z]

theorem Equation307_4284_4512_53866_implies_Equation41547 (G : Type*) [Magma G] (h307 : Equation307 G) (h4284 : Equation4284 G) (h4512 : Equation4512 G) (h53866 : Equation53866 G) : Equation41547 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1]; rw [h53866 X0 sK0 sK1]
  have l1 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h4284 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK1]
    conv => enter [1]; rw [l1 X0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation307_3261_4512_53866_53880_implies_Equation41550 (G : Type*) [Magma G] (h307 : Equation307 G) (h3261 : Equation3261 G) (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h53880 : Equation53880 G) : Equation41550 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [h3261 sK0 sK2]
    conv => enter [1]; rw [← h53866 sK0 (sK2 ◇ sK0) sK2]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l3 sK0 sK2]
    conv => enter [1]; rw [h53880 sK0 (sK2 ◇ sK0) X0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation3261_4284_53880_implies_Equation41568 (G : Type*) [Magma G] (h3261 : Equation3261 G) (h4284 : Equation4284 G) (h53880 : Equation53880 G) : Equation41568 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3261 sK0 X0]
    conv => enter [1, 2]; rw [h4284 X0 sK0]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4284 sK1 sK0]
    conv => enter [1]; rw [h53880 sK1 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation3261_4284_53876_implies_Equation41550 (G : Type*) [Magma G] (h3261 : Equation3261 G) (h4284 : Equation4284 G) (h53876 : Equation53876 G) : Equation41550 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3261 sK0 X0]
    conv => enter [1, 2]; rw [h4284 X0 sK0]
  have l1 : ∀ X0 sK0 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [← h4284 X0 sK0]
    conv => enter [1]; rw [h53876 X0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation3261_4512_54178_implies_Equation41568 (G : Type*) [Magma G] (h3261 : Equation3261 G) (h4512 : Equation4512 G) (h54178 : Equation54178 G) : Equation41568 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h54178 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  intro x y z
  conv => enter [1]; rw [h3261 x y]
  conv => enter [1]; rw [l4 x y x z]

theorem Equation307_4512_53818_implies_Equation3264 (G : Type*) [Magma G] (h307 : Equation307 G) (h4512 : Equation4512 G) (h53818 : Equation53818 G) : Equation3264 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h307 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53818 sK0 X0 sK2]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation307_4512_53818_implies_Equation41576 (G : Type*) [Magma G] (h307 : Equation307 G) (h4512 : Equation4512 G) (h53818 : Equation53818 G) : Equation41576 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h307 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
  have l1 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53818 sK1 X0 sK0]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1]
    conv => enter [1]; rw [l1 sK1 X0 sK0]
  have l3 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l2 sK1 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation3264_4512_implies_Equation41576 (G : Type*) [Magma G] (h3264 : Equation3264 G) (h4512 : Equation4512 G) : Equation41576 G := by
  have l0 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h3264 sK1 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation307_3264_implies_Equation53818 (G : Type*) [Magma G] (h307 : Equation307 G) (h3264 : Equation3264 G) : Equation53818 G := by
  intro x y z
  conv => enter [1]; rw [← h307 x]
  conv => enter [1]; rw [h3264 x y z]

@[equational_result]
theorem Equation323_implies_Equation41733 (G : Type*) [Magma G] (h323 : Equation323 G) : Equation41733 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1, 2]; rw [h323 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation326_implies_Equation41783 (G : Type*) [Magma G] (h326 : Equation326 G) : Equation41783 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h326 sK1 sK1]
    conv => enter [1, 2]; rw [h326 sK1 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h326 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation323_4512_41931_54318_implies_Equation333 (G : Type*) [Magma G] (h323 : Equation323 G) (h4512 : Equation4512 G) (h41931 : Equation41931 G) (h54318 : Equation54318 G) : Equation333 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h323 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1]; rw [h41931 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← h323 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41931 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [← h54318 (sK0 ◇ sK1) sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [← h54318 (sK0 ◇ sK1) sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [← h323 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h323 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation41769_54335_54339_implies_Equation325 (G : Type*) [Magma G] (h41769 : Equation41769 G) (h54335 : Equation54335 G) (h54339 : Equation54339 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h41769 X0 X1]
    conv => enter [1, 2]; rw [← h54335 X1 X0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h54339 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation323_4512_53870_implies_Equation41743 (G : Type*) [Magma G] (h323 : Equation323 G) (h4512 : Equation4512 G) (h53870 : Equation53870 G) : Equation41743 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h323 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53870 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h323 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [← h323 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h323 x (y ◇ (x ◇ y))]

theorem Equation326_4512_54172_implies_Equation41773 (G : Type*) [Magma G] (h326 : Equation326 G) (h4512 : Equation4512 G) (h54172 : Equation54172 G) : Equation41773 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1, 1, 2]; rw [h326 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [← h326 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h326 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h326 sK0 sK1]
    conv => enter [1]; rw [l5 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54172 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 ((sK0 ◇ sK1) ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation333_implies_Equation41931 (G : Type*) [Magma G] (h333 : Equation333 G) : Equation41931 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h333 sK1 sK0]
    conv => enter [1, 2]; rw [h333 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h333 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation325_326_implies_Equation41769 (G : Type*) [Magma G] (h325 : Equation325 G) (h326 : Equation326 G) : Equation41769 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h325 sK0 sK0]
    conv => enter [1]; rw [← h326 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation323_326_333_implies_Equation41887 (G : Type*) [Magma G] (h323 : Equation323 G) (h326 : Equation326 G) (h333 : Equation333 G) : Equation41887 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h323 sK0 sK1]
    conv => enter [1, 2]; rw [h326 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h333 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation323_325_implies_Equation41745 (G : Type*) [Magma G] (h323 : Equation323 G) (h325 : Equation325 G) : Equation41745 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h325 sK1 sK0]
    conv => enter [1]; rw [h323 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h325 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h325 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]
  conv => enter [1]; rw [h323 x (y ◇ (y ◇ x))]

theorem Equation315_4512_53846_implies_Equation3292 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) (h53846 : Equation53846 G) : Equation3292 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53846 sK0 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation312_315_4512_53846_implies_Equation41684 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h4512 : Equation4512 G) (h53846 : Equation53846 G) : Equation41684 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h315 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h312 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h315 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK1) sK1]
  have l5 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1]; rw [l2 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h53846 (sK0 ◇ sK1) sK2 X0]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 sK0 sK2 X0]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation312_4512_53846_implies_Equation41711 (G : Type*) [Magma G] (h312 : Equation312 G) (h4512 : Equation4512 G) (h53846 : Equation53846 G) : Equation41711 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h312 X0 X0]
    conv => enter [1]; rw [h53846 X0 X1 X2]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X3) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation312_53850_53880_implies_Equation41716 (G : Type*) [Magma G] (h312 : Equation312 G) (h53850 : Equation53850 G) (h53880 : Equation53880 G) : Equation41716 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h312 X0 X0]
    conv => enter [1]; rw [h53850 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1, 2]; rw [h53880 z x w]

theorem Equation308_53876_implies_Equation3265 (G : Type*) [Magma G] (h308 : Equation308 G) (h53876 : Equation53876 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [h308 x y]
  conv => enter [1]; rw [h53876 x y z]

theorem Equation308_4512_53819_implies_Equation41571 (G : Type*) [Magma G] (h308 : Equation308 G) (h4512 : Equation4512 G) (h53819 : Equation53819 G) : Equation41571 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [h53819 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
  intro x y z w
  conv => enter [1]; rw [h308 x w]
  conv => enter [1]; rw [l4 x w y z]

theorem Equation308_4512_53819_implies_Equation41577 (G : Type*) [Magma G] (h308 : Equation308 G) (h4512 : Equation4512 G) (h53819 : Equation53819 G) : Equation41577 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [h53819 X0 X1 X2]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [l0 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation308_310_53876_implies_Equation41578 (G : Type*) [Magma G] (h308 : Equation308 G) (h310 : Equation310 G) (h53876 : Equation53876 G) : Equation41578 G := by
  intro x y z w
  conv => enter [1]; rw [h310 x y]
  conv => enter [1, 2]; rw [h308 y z]
  conv => enter [1, 2]; rw [h53876 y z w]

theorem Equation315_53876_implies_Equation3274 (G : Type*) [Magma G] (h315 : Equation315 G) (h53876 : Equation53876 G) : Equation3274 G := by
  intro x y z
  conv => enter [1]; rw [h315 x y]
  conv => enter [1]; rw [h53876 y x z]

theorem Equation312_4512_53828_implies_Equation41613 (G : Type*) [Magma G] (h312 : Equation312 G) (h4512 : Equation4512 G) (h53828 : Equation53828 G) : Equation41613 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h312 X0 X0]
    conv => enter [1]; rw [h53828 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l0 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation312_53850_53951_implies_Equation41667 (G : Type*) [Magma G] (h312 : Equation312 G) (h53850 : Equation53850 G) (h53951 : Equation53951 G) : Equation41667 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h312 X0 X0]
    conv => enter [1]; rw [h53850 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y w]
  conv => enter [1, 2]; rw [h53951 w x z]

theorem Equation312_315_4512_53828_implies_Equation41716 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h4512 : Equation4512 G) (h53828 : Equation53828 G) : Equation41716 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h312 X0 X0]
    conv => enter [1]; rw [h53828 X0 X1 X2]
  have l1 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← l0 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [← l1 X1 X0 X2 X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  intro x y z w
  conv => enter [1]; rw [h315 x z]
  conv => enter [1]; rw [l4 z x y w]

theorem Equation308_53871_implies_Equation3260 (G : Type*) [Magma G] (h308 : Equation308 G) (h53871 : Equation53871 G) : Equation3260 G := by
  have l0 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h308 sK0 X0]
    conv => enter [1]; rw [h53871 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation308_53871_implies_Equation41553 (G : Type*) [Magma G] (h308 : Equation308 G) (h53871 : Equation53871 G) : Equation41553 G := by
  have l0 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [h308 sK1 X0]
    conv => enter [1]; rw [h53871 sK1 X0 (sK3 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation308_4512_53814_implies_Equation41567 (G : Type*) [Magma G] (h308 : Equation308 G) (h4512 : Equation4512 G) (h53814 : Equation53814 G) : Equation41567 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [h53814 X0 X1 X2]
  have l1 : ∀ X2 X0 X1 X3 : G, (X2 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l0 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation308_310_4512_53871_implies_Equation41571 (G : Type*) [Magma G] (h308 : Equation308 G) (h310 : Equation310 G) (h4512 : Equation4512 G) (h53871 : Equation53871 G) : Equation41571 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h310 sK1 (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ sK2 X0 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 X0 sK0
    conv => enter [1]; rw [h308 sK2 X0]
    conv => enter [1]; rw [h53871 sK2 X0 sK0]
  have l2 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [← l1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 sK2 sK2 X0]
  have l3 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ sK2) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h308 sK2 X0]
    conv => enter [1]; rw [← l2 sK2 sK3 sK0 X0]
  have l4 : ∀ sK2 sK3 sK0 X0 : G, (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l1 sK2 sK3 sK0]
    conv => enter [1]; rw [l3 sK2 sK3 sK0 X0]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0))) X0]
  have l6 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l5 sK1 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
  intro x y z w
  conv => enter [1]; rw [l6 x y z w]

theorem Equation312_315_3292_implies_Equation41684 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h3292 : Equation3292 G) : Equation41684 G := by
  have l0 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h315 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h312 sK1 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) sK2]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h315 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h3292 (sK0 ◇ sK1) sK2 X0]
  have l4 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l3 sK2 sK0 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation3292_4512_implies_Equation41711 (G : Type*) [Magma G] (h3292 : Equation3292 G) (h4512 : Equation4512 G) : Equation41711 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK1) = (sK2 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h3292 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK2 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation312_3292_implies_Equation41716 (G : Type*) [Magma G] (h312 : Equation312 G) (h3292 : Equation3292 G) : Equation41716 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK3 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h312 sK1 sK2]
    conv => enter [1, 2]; rw [h3292 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation312_3292_implies_Equation54244 (G : Type*) [Magma G] (h312 : Equation312 G) (h3292 : Equation3292 G) : Equation54244 G := by
  intro x y z
  conv => enter [1]; rw [← h312 y x]
  conv => enter [1]; rw [h3292 y z x]

theorem Equation308_3265_4512_implies_Equation41571 (G : Type*) [Magma G] (h308 : Equation308 G) (h3265 : Equation3265 G) (h4512 : Equation4512 G) : Equation41571 G := by
  have l0 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h3265 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l1 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l0 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, ((X0 ◇ X0) ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X1 X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
  intro x y z w
  conv => enter [1]; rw [h308 x w]
  conv => enter [1]; rw [l3 x w y z]

theorem Equation3265_4512_implies_Equation41577 (G : Type*) [Magma G] (h3265 : Equation3265 G) (h4512 : Equation4512 G) : Equation41577 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h3265 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation310_3265_implies_Equation41578 (G : Type*) [Magma G] (h310 : Equation310 G) (h3265 : Equation3265 G) : Equation41578 G := by
  have l0 : ∀ X1 X0 sK1 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK1]
  have l1 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [l0 X0 X1 sK1]
  have l2 : ∀ X0 sK1 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK3))) := by
    intro X0 sK1 sK3 sK0
    conv => enter [1]; rw [← h310 X0 sK1]
    conv => enter [1]; rw [h3265 X0 sK3 sK0]
  have l3 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 X0 sK1 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK1 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h310 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation308_3265_implies_Equation53885 (G : Type*) [Magma G] (h308 : Equation308 G) (h3265 : Equation3265 G) : Equation53885 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h308 sK0 sK1]
    conv => enter [1]; rw [h3265 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation3274_4512_implies_Equation41613 (G : Type*) [Magma G] (h3274 : Equation3274 G) (h4512 : Equation4512 G) : Equation41613 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h3274 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation312_3274_implies_Equation41667 (G : Type*) [Magma G] (h312 : Equation312 G) (h3274 : Equation3274 G) : Equation41667 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h312 sK1 sK2]
    conv => enter [1, 2]; rw [h3274 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation315_3274_4512_implies_Equation41716 (G : Type*) [Magma G] (h315 : Equation315 G) (h3274 : Equation3274 G) (h4512 : Equation4512 G) : Equation41716 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3274 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [← l0 X1 X0 X2 X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  intro x y z w
  conv => enter [1]; rw [h315 x z]
  conv => enter [1]; rw [l3 z x y w]

theorem Equation315_3274_implies_Equation53963 (G : Type*) [Magma G] (h315 : Equation315 G) (h3274 : Equation3274 G) : Equation53963 G := by
  have l0 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← h315 sK2 sK1]
    conv => enter [1]; rw [h3274 sK2 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

@[equational_result]
theorem Equation3260_implies_Equation41553 (G : Type*) [Magma G] (h3260 : Equation3260 G) : Equation41553 G := by
  intro x y z w
  conv => enter [1]; rw [h3260 x y (z ◇ w)]

theorem Equation3260_4512_implies_Equation41567 (G : Type*) [Magma G] (h3260 : Equation3260 G) (h4512 : Equation4512 G) : Equation41567 G := by
  have l0 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [h3260 sK1 (X0 ◇ X1) sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation310_3260_implies_Equation41571 (G : Type*) [Magma G] (h310 : Equation310 G) (h3260 : Equation3260 G) : Equation41571 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [← h310 X0 X1]
    conv => enter [1]; rw [h310 X0 sK1]
  have l1 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h3260 sK2 sK3 sK0]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h310 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation310_3260_implies_Equation54184 (G : Type*) [Magma G] (h310 : Equation310 G) (h3260 : Equation3260 G) : Equation54184 G := by
  have l0 : ∀ sK1 sK0 X0 sK3 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK3))) := by
    intro sK1 sK0 X0 sK3
    conv => enter [1]; rw [← h310 sK1 sK0]
    conv => enter [1]; rw [h3260 sK1 X0 sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation312_3264_implies_Equation41613 (G : Type*) [Magma G] (h312 : Equation312 G) (h3264 : Equation3264 G) : Equation41613 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h312 sK1 sK2]
    conv => enter [1, 2]; rw [h3264 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation315_3264_4512_implies_Equation41711 (G : Type*) [Magma G] (h315 : Equation315 G) (h3264 : Equation3264 G) (h4512 : Equation4512 G) : Equation41711 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3264 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 X3]
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  intro x y z w
  conv => enter [1]; rw [h315 x y]
  conv => enter [1]; rw [l3 y x z w]

theorem Equation308_3264_4512_implies_Equation41567 (G : Type*) [Magma G] (h308 : Equation308 G) (h3264 : Equation3264 G) (h4512 : Equation4512 G) : Equation41567 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
    conv => enter [1, 1]; rw [← h3264 X0 X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h308 X0 X3]
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 X0 X3]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation310_3264_implies_Equation41577 (G : Type*) [Magma G] (h310 : Equation310 G) (h3264 : Equation3264 G) : Equation41577 G := by
  have l0 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [h310 X0 sK2]
    conv => enter [1, 2]; rw [h3264 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation315_4512_53854_implies_Equation3300 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation3300 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h315 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 X1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53854 sK1 X0 X1 sK0]
  have l2 : ∀ sK1 X0 X1 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 X1 sK0
    conv => enter [1]; rw [l0 sK1 sK1]
    conv => enter [1]; rw [l1 sK1 X0 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

theorem Equation312_315_4512_53854_implies_Equation41726 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h4512 : Equation4512 G) (h53854 : Equation53854 G) : Equation41726 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← h315 sK2 sK0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h312 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l2 : ∀ sK2 X0 sK0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 X0 sK0
    conv => enter [1, 1]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X0]
  have l3 : ∀ X0 sK2 : G, (X0 ◇ X0) = ((sK2 ◇ sK2) ◇ X0) := by
    intro X0 sK2
    conv => enter [1]; rw [h315 X0 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 X0]
  have l4 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [l3 (sK0 ◇ sK2) sK2]
  have l5 : ∀ sK2 sK0 X0 X1 sK1 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0 X1 sK1
    conv => enter [1]; rw [l2 sK2 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [h53854 (sK0 ◇ sK2) X0 X1 sK1]
  have l6 : ∀ sK2 X0 X1 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l4 sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK0 X0 X1 sK1]
  intro x y z w u
  conv => enter [1]; rw [l6 x y z w u]

theorem Equation308_53821_implies_Equation3267 (G : Type*) [Magma G] (h308 : Equation308 G) (h53821 : Equation53821 G) : Equation3267 G := by
  have l0 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [h53821 X0 X1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z w]

theorem Equation308_53821_implies_Equation41580 (G : Type*) [Magma G] (h308 : Equation308 G) (h53821 : Equation53821 G) : Equation41580 G := by
  have l0 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h308 X0 X0]
    conv => enter [1]; rw [h53821 X0 X1 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l0 x y z w u]

theorem Equation312_315_3300_implies_Equation41726 (G : Type*) [Magma G] (h312 : Equation312 G) (h315 : Equation315 G) (h3300 : Equation3300 G) : Equation41726 G := by
  have l0 : ∀ sK0 sK2 : G, ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK2) sK0]
    conv => enter [1, 2]; rw [← h315 sK2 sK0]
  have l1 : ∀ sK2 sK0 : G, (sK2 ◇ sK2) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h312 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l2 : ∀ sK2 X0 X1 sK1 sK0 : G, (sK2 ◇ sK2) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 X0 X1 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK0]
    conv => enter [1]; rw [h3300 (sK0 ◇ sK2) X0 X1 sK1]
  intro x y z w u
  conv => enter [1]; rw [l2 x y z w u]

theorem Equation315_3300_implies_Equation53946 (G : Type*) [Magma G] (h315 : Equation315 G) (h3300 : Equation3300 G) : Equation53946 G := by
  have l0 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [← h315 sK2 sK1]
    conv => enter [1]; rw [h3300 sK2 X0 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l0 x y z x w]

theorem Equation310_3267_implies_Equation41580 (G : Type*) [Magma G] (h310 : Equation310 G) (h3267 : Equation3267 G) : Equation41580 G := by
  have l0 : ∀ X1 X0 sK2 : G, (X1 ◇ X1) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 sK2
    conv => enter [1]; rw [h310 X1 X0]
    conv => enter [1, 2]; rw [h310 X0 sK2]
  have l1 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [← h310 X0 sK2]
    conv => enter [1]; rw [l0 X0 X1 sK2]
  have l2 : ∀ X0 sK2 sK4 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK2 sK4 sK1 sK0
    conv => enter [1]; rw [← h310 X0 sK2]
    conv => enter [1]; rw [h3267 X0 sK4 sK1 sK0]
  have l3 : ∀ X0 sK2 sK3 sK4 sK1 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 X0 sK2 sK3]
    conv => enter [1, 2]; rw [l2 sK3 sK2 sK4 sK1 sK0]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK2) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h310 sK2 sK2]
    conv => enter [1]; rw [l3 sK2 sK2 sK3 sK4 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation308_3267_implies_Equation53878 (G : Type*) [Magma G] (h308 : Equation308 G) (h3267 : Equation3267 G) : Equation53878 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h3267 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h308 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [← l0 x y z w]

@[equational_result]
theorem Equation47_implies_Equation41783 (G : Type*) [Magma G] (h47 : Equation47 G) : Equation41783 G := by
  intro x y
  conv => enter [1, 2]; rw [h47 y]

theorem Equation47_4512_implies_Equation41733 (G : Type*) [Magma G] (h47 : Equation47 G) (h4512 : Equation4512 G) : Equation41733 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h47 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation47_4512_41849_42223_implies_Equation75 (G : Type*) [Magma G] (h47 : Equation47 G) (h4512 : Equation4512 G) (h41849 : Equation41849 G) (h42223 : Equation42223 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h47 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2]; rw [← h41849 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h42223 X1 ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h41849 X1 (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X1)) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h41849 X1 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 X0]
    conv => enter [1]; rw [← h47 X1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h47 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← h41849 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation47_4512_41799_41849_implies_Equation56 (G : Type*) [Magma G] (h47 : Equation47 G) (h4512 : Equation4512 G) (h41799 : Equation41799 G) (h41849 : Equation41849 G) : Equation56 G := by
  have l0 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h47 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [l0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l1 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h47 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2, 2]; rw [← h41799 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h41849 X0 ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1, 2]; rw [← h41849 X0 ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0) X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h41849 X0 X0 X1]
    conv => enter [1]; rw [← l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 X1]
    conv => enter [1]; rw [← h47 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l4 sK0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l20 x y]

@[equational_result]
theorem Equation75_implies_Equation41849 (G : Type*) [Magma G] (h75 : Equation75 G) : Equation41849 G := by
  intro x y z
  conv => enter [1, 2]; rw [h75 y z]

@[equational_result]
theorem Equation75_implies_Equation42223 (G : Type*) [Magma G] (h75 : Equation75 G) : Equation42223 G := by
  intro x y z
  conv => enter [1]; rw [h75 (x ◇ y) z]

@[equational_result]
theorem Equation56_implies_Equation41799 (G : Type*) [Magma G] (h56 : Equation56 G) : Equation41799 G := by
  intro x y z
  conv => enter [1, 2]; rw [h56 y z]

theorem Equation43_41849_implies_Equation41999 (G : Type*) [Magma G] (h43 : Equation43 G) (h41849 : Equation41849 G) : Equation41999 G := by
  intro x y z
  conv => enter [1]; rw [h43 x y]
  conv => enter [1]; rw [h41849 y x z]

theorem Equation40_41659_implies_Equation41607 (G : Type*) [Magma G] (h40 : Equation40 G) (h41659 : Equation41659 G) : Equation41607 G := by
  intro x y z
  conv => enter [1]; rw [h40 x z]
  conv => enter [1]; rw [h41659 z y x]

theorem Equation40_41551_implies_Equation41674 (G : Type*) [Magma G] (h40 : Equation40 G) (h41551 : Equation41551 G) : Equation41674 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41551 y z x]

theorem Equation40_41605_implies_Equation41661 (G : Type*) [Magma G] (h40 : Equation40 G) (h41605 : Equation41605 G) : Equation41661 G := by
  intro x y z
  conv => enter [1]; rw [h40 x z]
  conv => enter [1]; rw [h41605 z y x]

theorem Equation40_41565_implies_Equation41661 (G : Type*) [Magma G] (h40 : Equation40 G) (h41565 : Equation41565 G) : Equation41661 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41565 y z x]

theorem Equation40_41597_implies_Equation41674 (G : Type*) [Magma G] (h40 : Equation40 G) (h41597 : Equation41597 G) : Equation41674 G := by
  intro x y z
  conv => enter [1]; rw [h40 x z]
  conv => enter [1]; rw [h41597 z y x]

theorem Equation40_41566_implies_Equation41607 (G : Type*) [Magma G] (h40 : Equation40 G) (h41566 : Equation41566 G) : Equation41607 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41566 y x z]

theorem Equation40_41568_implies_Equation41602 (G : Type*) [Magma G] (h40 : Equation40 G) (h41568 : Equation41568 G) : Equation41602 G := by
  intro x y z
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41568 y x z]

theorem Equation40_41716_implies_Equation41604 (G : Type*) [Magma G] (h40 : Equation40 G) (h41716 : Equation41716 G) : Equation41604 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x w]
  conv => enter [1]; rw [h41716 w y x z]

theorem Equation40_41571_implies_Equation41604 (G : Type*) [Magma G] (h40 : Equation40 G) (h41571 : Equation41571 G) : Equation41604 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41571 y x z w]

theorem Equation40_41711_implies_Equation41608 (G : Type*) [Magma G] (h40 : Equation40 G) (h41711 : Equation41711 G) : Equation41608 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x w]
  conv => enter [1]; rw [h41711 w y x z]

theorem Equation40_41577_implies_Equation41708 (G : Type*) [Magma G] (h40 : Equation40 G) (h41577 : Equation41577 G) : Equation41708 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41577 y z w x]

theorem Equation40_41567_implies_Equation41608 (G : Type*) [Magma G] (h40 : Equation40 G) (h41567 : Equation41567 G) : Equation41608 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41567 y x z w]

theorem Equation40_41613_implies_Equation41708 (G : Type*) [Magma G] (h40 : Equation40 G) (h41613 : Equation41613 G) : Equation41708 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x z]
  conv => enter [1]; rw [h41613 z y w x]

theorem Equation40_41550_implies_Equation41685 (G : Type*) [Magma G] (h40 : Equation40 G) (h41550 : Equation41550 G) : Equation41685 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41550 y z w]

theorem Equation40_41576_implies_Equation41668 (G : Type*) [Magma G] (h40 : Equation40 G) (h41576 : Equation41576 G) : Equation41668 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41576 y z x w]

theorem Equation40_41667_implies_Equation41709 (G : Type*) [Magma G] (h40 : Equation40 G) (h41667 : Equation41667 G) : Equation41709 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x w]
  conv => enter [1]; rw [h41667 w y z x]

theorem Equation40_41553_implies_Equation41600 (G : Type*) [Magma G] (h40 : Equation40 G) (h41553 : Equation41553 G) : Equation41600 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41553 y x z w]

theorem Equation40_41578_implies_Equation41709 (G : Type*) [Magma G] (h40 : Equation40 G) (h41578 : Equation41578 G) : Equation41709 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41578 y z w x]

theorem Equation40_41684_implies_Equation41600 (G : Type*) [Magma G] (h40 : Equation40 G) (h41684 : Equation41684 G) : Equation41600 G := by
  intro x y z w
  conv => enter [1]; rw [h40 x w]
  conv => enter [1]; rw [h41684 w y x z]

theorem Equation40_41726_implies_Equation41671 (G : Type*) [Magma G] (h40 : Equation40 G) (h41726 : Equation41726 G) : Equation41671 G := by
  intro x y z w u
  conv => enter [1]; rw [h40 x u]
  conv => enter [1]; rw [h41726 u y z x w]

theorem Equation40_41580_implies_Equation41671 (G : Type*) [Magma G] (h40 : Equation40 G) (h41580 : Equation41580 G) : Equation41671 G := by
  intro x y z w u
  conv => enter [1]; rw [h40 x y]
  conv => enter [1]; rw [h41580 y z x w u]

theorem Equation323_5099_54318_implies_Equation5 (G : Type*) [Magma G] (h323 : Equation323 G) (h5099 : Equation5099 G) (h54318 : Equation54318 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h54318 X1 X1 X0]
    conv => enter [1]; rw [← h5099 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54318 X1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h54318 X1 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h323 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation3_4798_54335_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h4798 : Equation4798 G) (h54335 : Equation54335 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h54335 X1 X1 X1]
    conv => enter [1]; rw [← h4798 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h54335 X1 X1 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h54335 X0 X1 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h3 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation2_implies_Equation6 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation6 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ y)]

@[equational_result]
theorem Equation6_implies_Equation2 (G : Type*) [Magma G] (h6 : Equation6 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h6 X0 X0]
    conv => enter [1]; rw [← h6 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation7 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation7 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ z)]

@[equational_result]
theorem Equation7_implies_Equation2 (G : Type*) [Magma G] (h7 : Equation7 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h7 X0 X0 X0]
    conv => enter [1]; rw [← h7 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation15 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation15 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation15_implies_Equation2 (G : Type*) [Magma G] (h15 : Equation15 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h15 X0 X2 X1]
    conv => enter [1]; rw [← h15 X2 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ X0) X0]
    conv => enter [1]; rw [← h15 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation17 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation17 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation17_implies_Equation2 (G : Type*) [Magma G] (h17 : Equation17 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h17 X0 X0]
    conv => enter [1]; rw [← h17 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation18 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation18 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation18_implies_Equation2 (G : Type*) [Magma G] (h18 : Equation18 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h18 X0 X0 X0]
    conv => enter [1]; rw [← h18 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation20 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation20 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation20_implies_Equation2 (G : Type*) [Magma G] (h20 : Equation20 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h20 X0 X0 X0]
    conv => enter [1]; rw [← h20 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation21 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation21 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation21_implies_Equation2 (G : Type*) [Magma G] (h21 : Equation21 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h21 X0 X0 X0]
    conv => enter [1]; rw [← h21 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation22 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation22 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation22_implies_Equation2 (G : Type*) [Magma G] (h22 : Equation22 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h22 X0 X0 X0 X0]
    conv => enter [1]; rw [← h22 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation63 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation63 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ y)))]

theorem Equation63_4512_implies_Equation2 (G : Type*) [Magma G] (h63 : Equation63 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h63 X0 X1]
    conv => enter [1]; rw [← h63 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h63 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h63 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h63 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation64 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation64 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ z)))]

@[equational_result]
theorem Equation64_implies_Equation2 (G : Type*) [Magma G] (h64 : Equation64 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h64 X0 X2 X1]
    conv => enter [1]; rw [← h64 X2 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h64 X0 X0 X1]
    conv => enter [1]; rw [← h64 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h64 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation67 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation67 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation67_implies_Equation2 (G : Type*) [Magma G] (h67 : Equation67 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h67 X0 X1 X0]
    conv => enter [1]; rw [← h67 X1 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation69 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation69 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ y)))]

theorem Equation69_4512_implies_Equation2 (G : Type*) [Magma G] (h69 : Equation69 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h69 X0 X2 X1]
    conv => enter [1]; rw [← h69 X3 (X0 ◇ (X1 ◇ X2)) X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X3 : G, (X1 ◇ X2) = X3 := by
    intro X1 X2 X3
    conv => enter [1]; rw [h69 (X1 ◇ X2) X1 X3]
    conv => enter [1]; rw [l1 X1 X1 X2 X3]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 (X2 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h69 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation70 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation70 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ z)))]

@[equational_result]
theorem Equation70_implies_Equation2 (G : Type*) [Magma G] (h70 : Equation70 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h70 X0 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h70 X2 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l0 X2 X0 X0]
    conv => enter [1]; rw [← h70 X2 X1 X0]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 (X2 ◇ X0) X0]
    conv => enter [1]; rw [l0 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation71 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation71 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ w)))]

@[equational_result]
theorem Equation71_implies_Equation2 (G : Type*) [Magma G] (h71 : Equation71 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h71 X0 X2 X1 X1]
    conv => enter [1]; rw [← h71 X2 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h71 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation74 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation74 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ z)))]

@[equational_result]
theorem Equation74_implies_Equation2 (G : Type*) [Magma G] (h74 : Equation74 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h74 X0 X2 X1]
    conv => enter [1]; rw [← h74 X2 X1 (X2 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h74 X0 X1 X1]
    conv => enter [1]; rw [← h74 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation76 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation76 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation76_implies_Equation2 (G : Type*) [Magma G] (h76 : Equation76 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h76 X0 X0]
    conv => enter [1]; rw [← h76 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation77 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation77 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ z)))]

@[equational_result]
theorem Equation77_implies_Equation2 (G : Type*) [Magma G] (h77 : Equation77 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h77 X0 X0 X0]
    conv => enter [1]; rw [← h77 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation79 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation79 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ y)))]

@[equational_result]
theorem Equation79_implies_Equation2 (G : Type*) [Magma G] (h79 : Equation79 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h79 X0 X0 X0]
    conv => enter [1]; rw [← h79 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation80 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation80 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ z)))]

@[equational_result]
theorem Equation80_implies_Equation2 (G : Type*) [Magma G] (h80 : Equation80 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h80 X0 X0 X0]
    conv => enter [1]; rw [← h80 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation81 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation81 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ w)))]

@[equational_result]
theorem Equation81_implies_Equation2 (G : Type*) [Magma G] (h81 : Equation81 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h81 X0 X0 X0 X0]
    conv => enter [1]; rw [← h81 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation83 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation83 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ y)))]

theorem Equation83_4512_implies_Equation2 (G : Type*) [Magma G] (h83 : Equation83 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h83 X0 X2 X1]
    conv => enter [1]; rw [← h83 X2 (X1 ◇ (X0 ◇ X2)) X3]
  have l1 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) = X2 := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X2 X3]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0 X2 X3]
  have l3 : ∀ X1 X3 X2 : G, (X1 ◇ X3) = X2 := by
    intro X1 X3 X2
    conv => enter [1, 2]; rw [h83 X3 X1 X2]
    conv => enter [1]; rw [l2 X1 X1 X2 X3]
  have l4 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l3 X0 (X0 ◇ (X3 ◇ X0)) X0]
    conv => enter [1]; rw [← h83 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation84 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation84 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ z)))]

@[equational_result]
theorem Equation84_implies_Equation2 (G : Type*) [Magma G] (h84 : Equation84 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h84 X0 (X0 ◇ X2) X2]
    conv => enter [1]; rw [← h84 X2 X1 (X0 ◇ X2)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ X0)) X0]
    conv => enter [1]; rw [← h84 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation85 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation85 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ w)))]

@[equational_result]
theorem Equation85_implies_Equation2 (G : Type*) [Magma G] (h85 : Equation85 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h85 X0 X1 X3 X1]
    conv => enter [1]; rw [← h85 X3 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ X0)) X0]
    conv => enter [1]; rw [← h85 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation87 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation87 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ y)))]

@[equational_result]
theorem Equation87_implies_Equation2 (G : Type*) [Magma G] (h87 : Equation87 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h87 X0 X0 X0]
    conv => enter [1]; rw [← h87 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation88 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation88 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ z)))]

@[equational_result]
theorem Equation88_implies_Equation2 (G : Type*) [Magma G] (h88 : Equation88 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h88 X0 X0 X0]
    conv => enter [1]; rw [← h88 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation89 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation89 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ w)))]

@[equational_result]
theorem Equation89_implies_Equation2 (G : Type*) [Magma G] (h89 : Equation89 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h89 X0 X0 X0 X0]
    conv => enter [1]; rw [← h89 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation91 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation91 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ y)))]

@[equational_result]
theorem Equation91_implies_Equation2 (G : Type*) [Magma G] (h91 : Equation91 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h91 X0 X0 X0]
    conv => enter [1]; rw [← h91 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation92 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation92 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ z)))]

@[equational_result]
theorem Equation92_implies_Equation2 (G : Type*) [Magma G] (h92 : Equation92 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h92 X0 X0 X0]
    conv => enter [1]; rw [← h92 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation93 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation93 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ w)))]

@[equational_result]
theorem Equation93_implies_Equation2 (G : Type*) [Magma G] (h93 : Equation93 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h93 X0 X0 X0 X0]
    conv => enter [1]; rw [← h93 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation95 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation95 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ y)))]

@[equational_result]
theorem Equation95_implies_Equation2 (G : Type*) [Magma G] (h95 : Equation95 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h95 X0 X0 X0 X0]
    conv => enter [1]; rw [← h95 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation96 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation96 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ z)))]

@[equational_result]
theorem Equation96_implies_Equation2 (G : Type*) [Magma G] (h96 : Equation96 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h96 X0 X0 X0 X0]
    conv => enter [1]; rw [← h96 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation97 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation97 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ w)))]

@[equational_result]
theorem Equation97_implies_Equation2 (G : Type*) [Magma G] (h97 : Equation97 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h97 X0 X0 X0 X0]
    conv => enter [1]; rw [← h97 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation98 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation98 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation98_implies_Equation2 (G : Type*) [Magma G] (h98 : Equation98 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h98 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h98 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation465 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation465 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ z))))]

@[equational_result]
theorem Equation465_implies_Equation2 (G : Type*) [Magma G] (h465 : Equation465 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h465 X0 X2 X1]
    conv => enter [1]; rw [← h465 X2 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h465 X0 X0 X1]
    conv => enter [1]; rw [← h465 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 2, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l2 X2 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h465 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation467 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation467 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ y))))]

theorem Equation467_4512_implies_Equation2 (G : Type*) [Magma G] (h467 : Equation467 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h467 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 (X1 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [← h467 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h467 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l4 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [l4 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [← h467 X1 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X1 (X0 ◇ (X1 ◇ X0))]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X1)) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l10 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l10 X1 X1]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X1) X1 X0]
    conv => enter [1, 2, 2]; rw [l10 (X0 ◇ X1) X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X1]
    conv => enter [1]; rw [← l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l17 X1 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 X0]
    conv => enter [1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation2_implies_Equation468 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation468 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ z))))]

theorem Equation468_4512_implies_Equation2 (G : Type*) [Magma G] (h468 : Equation468 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h468 X0 X1 X0]
    conv => enter [1]; rw [← h468 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h468 X0 X0 X0]
    conv => enter [1]; rw [← h468 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h468 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l0 X0 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h468 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation470 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation470 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ y))))]

theorem Equation470_4512_implies_Equation2 (G : Type*) [Magma G] (h470 : Equation470 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X0))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h470 X0 X2 X1]
    conv => enter [1]; rw [← h470 X3 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h470 X0 X2 X1]
    conv => enter [1]; rw [← h470 X2 (X0 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) (X2 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) (X3 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 (X2 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X3 : G, (X0 ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [l5 X0 X0 X0 X3]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h470 X0 X2 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l6 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l7 X2 X0 X1]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l6 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l10 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l9 X0 (X2 ◇ (X2 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h470 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation471 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation471 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ z))))]

@[equational_result]
theorem Equation471_implies_Equation2 (G : Type*) [Magma G] (h471 : Equation471 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h471 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X1]
    conv => enter [1]; rw [← h471 X2 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l0 X2 X0 X1]
    conv => enter [1]; rw [l0 X1 X2 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X0 X0]
    conv => enter [1]; rw [← h471 X0 X1 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l2 X2 X0]
    conv => enter [1]; rw [l1 X2 X2 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation472 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation472 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ w))))]

@[equational_result]
theorem Equation472_implies_Equation2 (G : Type*) [Magma G] (h472 : Equation472 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h472 X0 X2 X1 X1]
    conv => enter [1]; rw [← h472 X2 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h472 X0 X0 X1 X1]
    conv => enter [1]; rw [← h472 X0 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h472 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation474 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation474 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ y))))]

theorem Equation474_4512_implies_Equation2 (G : Type*) [Magma G] (h474 : Equation474 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h474 X0 X1]
    conv => enter [1]; rw [← h474 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h474 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h474 X0 X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← l9 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l7 X1 X0]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l9 X0 X1]
    conv => enter [1]; rw [← h474 X0 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l10 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l17 X1 X0]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation2_implies_Equation475 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation475 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ z))))]

@[equational_result]
theorem Equation475_implies_Equation2 (G : Type*) [Magma G] (h475 : Equation475 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h475 X0 X1 X0]
    conv => enter [1]; rw [← h475 X1 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation478 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation478 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ z))))]

@[equational_result]
theorem Equation478_implies_Equation2 (G : Type*) [Magma G] (h478 : Equation478 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h478 X0 X0 X0]
    conv => enter [1]; rw [← h478 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h478 X0 X0 X0]
    conv => enter [1]; rw [← h478 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h478 (X0 ◇ X1) X0 X1]
    conv => enter [1, 2]; rw [l0 (X0 ◇ X1) X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation480 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation480 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ y))))]

theorem Equation480_4512_implies_Equation2 (G : Type*) [Magma G] (h480 : Equation480 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h480 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h480 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h480 X1 X0 X1]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation482 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation482 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ w))))]

@[equational_result]
theorem Equation482_implies_Equation2 (G : Type*) [Magma G] (h482 : Equation482 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h482 X0 X1 X0 X0]
    conv => enter [1]; rw [← h482 X1 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation484 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation484 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ y))))]

theorem Equation484_4512_implies_Equation2 (G : Type*) [Magma G] (h484 : Equation484 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h484 X0 X1 X1]
    conv => enter [1]; rw [← h484 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h484 X0 X1 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation485 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation485 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ z))))]

theorem Equation485_4512_implies_Equation2 (G : Type*) [Magma G] (h485 : Equation485 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X0))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h485 X0 X2 X3]
    conv => enter [1]; rw [← h485 X2 X1 (X0 ◇ (X3 ◇ (X0 ◇ X3)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h485 X0 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h485 X0 X1 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X3 ◇ (X0 ◇ X3)) X0]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ X3) ◇ X0))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 (X0 ◇ X3) X0]
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X3 X0]
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
  have l5 : ∀ X1 X2 X3 : G, (X1 ◇ (X2 ◇ X3)) = X2 := by
    intro X1 X2 X3
    conv => enter [1, 2, 2]; rw [h485 X3 X1 X1]
    conv => enter [1]; rw [l4 X1 X2 X1 X3]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ X2))) = (X1 ◇ X0) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ (X2 ◇ (X0 ◇ X2)))]
    conv => enter [1, 2]; rw [← h485 X0 (X0 ◇ (X2 ◇ (X0 ◇ X2))) X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l6 X0 X2 X1]
    conv => enter [1]; rw [l5 X0 X2 (X0 ◇ X2)]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 X0 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l1 X0 X2]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation486 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation486 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ w))))]

@[equational_result]
theorem Equation486_implies_Equation2 (G : Type*) [Magma G] (h486 : Equation486 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h486 X0 X2 X2 X1]
    conv => enter [1]; rw [← h486 X2 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X2 ◇ X0))) X0]
    conv => enter [1]; rw [← h486 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation488 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation488 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ y))))]

theorem Equation488_4512_implies_Equation2 (G : Type*) [Magma G] (h488 : Equation488 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h488 (X0 ◇ (X1 ◇ X1)) X1 X0]
    conv => enter [1]; rw [← h488 X2 (X0 ◇ (X1 ◇ X1)) X1]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h488 X0 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [← h488 X1 (X1 ◇ X1) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X2 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 (X2 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X1 (X2 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l5 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h488 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation490 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation490 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ w))))]

@[equational_result]
theorem Equation490_implies_Equation2 (G : Type*) [Magma G] (h490 : Equation490 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h490 X0 X2 X1 X1]
    conv => enter [1]; rw [← h490 X2 X1 X0 (X2 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h490 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation493 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation493 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ z))))]

theorem Equation493_4512_implies_Equation2 (G : Type*) [Magma G] (h493 : Equation493 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h493 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h493 X2 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h493 X2 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X2 X0]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X2 X3 X0 X1]
  have l4 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X3 := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l3 X3 X3 X0 X1]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l4 X3 X0 X1]
  have l6 : ∀ X1 X0 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := by
    intro X1 X0 X3
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l5 X0 X1 X3]
  have l7 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l6 X1 X0 X3]
  have l8 : ∀ X1 X0 X3 : G, (X1 ◇ (X0 ◇ X1)) = X3 := by
    intro X1 X0 X3
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l7 X0 X1 X3]
  have l9 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l8 X1 X0 X3]
  have l10 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l9 X0 X2 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation494 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation494 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ w))))]

@[equational_result]
theorem Equation494_implies_Equation2 (G : Type*) [Magma G] (h494 : Equation494 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h494 X0 X2 X0 X1]
    conv => enter [1]; rw [← h494 X2 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h494 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation496 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation496 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ y))))]

@[equational_result]
theorem Equation496_implies_Equation2 (G : Type*) [Magma G] (h496 : Equation496 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h496 X0 X2 X1 X1]
    conv => enter [1]; rw [← h496 X2 (X1 ◇ X2) X0 X1]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h496 X2 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation497 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation497 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ z))))]

@[equational_result]
theorem Equation497_implies_Equation2 (G : Type*) [Magma G] (h497 : Equation497 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h497 (X0 ◇ X1) X3 X1 X0]
    conv => enter [1]; rw [← h497 X3 X2 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X2 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h497 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation498 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation498 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ w))))]

@[equational_result]
theorem Equation498_implies_Equation2 (G : Type*) [Magma G] (h498 : Equation498 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h498 X0 X2 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h498 X2 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h498 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation499 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation499 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ u))))]

@[equational_result]
theorem Equation499_implies_Equation2 (G : Type*) [Magma G] (h499 : Equation499 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h499 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h499 X2 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h499 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation501 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation501 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ y))))]

theorem Equation501_4512_implies_Equation2 (G : Type*) [Magma G] (h501 : Equation501 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h501 X0 X1]
    conv => enter [1]; rw [← h501 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X1) ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h501 X1 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h501 X0 X0]
    conv => enter [1]; rw [l7 X0 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l8 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l8 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l9 X1 X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l12 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 2]; rw [← h501 X0 X1]
  have l14 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l12 X2 (X0 ◇ X1)]
  have l15 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [← h501 X0 (X1 ◇ X0)]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 ((X1 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l17 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [l18 X1 (X0 ◇ ((X0 ◇ X1) ◇ X0))]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l20 X1 X0]
    conv => enter [1]; rw [l12 X0 (X0 ◇ X1)]
  have l22 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 X1 X1]
    conv => enter [1]; rw [l21 X0 X1]
  intro x y
  conv => enter [1]; rw [l22 x y]

@[equational_result]
theorem Equation2_implies_Equation502 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation502 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ z))))]

@[equational_result]
theorem Equation502_implies_Equation2 (G : Type*) [Magma G] (h502 : Equation502 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h502 X0 X2 X1]
    conv => enter [1]; rw [← h502 X2 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X2 ◇ X0)) X0]
    conv => enter [1]; rw [← h502 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation505 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation505 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ z))))]

@[equational_result]
theorem Equation505_implies_Equation2 (G : Type*) [Magma G] (h505 : Equation505 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h505 X0 X1 X1]
    conv => enter [1]; rw [← h505 X2 X1 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h505 X0 X1 X1]
    conv => enter [1]; rw [← h505 X1 X1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X2 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X2 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation507 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation507 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ y))))]

theorem Equation507_4512_implies_Equation2 (G : Type*) [Magma G] (h507 : Equation507 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h507 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X3 X4 (X0 ◇ X1) X2]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h507 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  have l3 : ∀ X3 X4 : G, X3 = X4 := by
    intro X3 X4
    conv => enter [1]; rw [← l2 X3 (X3 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3)))))]
    conv => enter [1]; rw [l1 X3 X4 X3 X3 X3]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation509 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation509 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ w))))]

@[equational_result]
theorem Equation509_implies_Equation2 (G : Type*) [Magma G] (h509 : Equation509 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h509 X0 X2 X1 X1]
    conv => enter [1]; rw [← h509 X2 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h509 X0 X1 X1 X1]
    conv => enter [1]; rw [← h509 X1 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation512 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation512 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ z))))]

@[equational_result]
theorem Equation512_implies_Equation2 (G : Type*) [Magma G] (h512 : Equation512 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h512 X0 X2 X1]
    conv => enter [1]; rw [← h512 X2 X1 (X2 ◇ (X2 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h512 X0 X1 X1]
    conv => enter [1]; rw [← h512 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation514 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation514 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation514_implies_Equation2 (G : Type*) [Magma G] (h514 : Equation514 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h514 X0 X0]
    conv => enter [1]; rw [← h514 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation515 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation515 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ z))))]

@[equational_result]
theorem Equation515_implies_Equation2 (G : Type*) [Magma G] (h515 : Equation515 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h515 X0 X0 X0]
    conv => enter [1]; rw [← h515 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation517 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation517 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ y))))]

@[equational_result]
theorem Equation517_implies_Equation2 (G : Type*) [Magma G] (h517 : Equation517 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h517 X0 X0 X0]
    conv => enter [1]; rw [← h517 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation518 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation518 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ z))))]

@[equational_result]
theorem Equation518_implies_Equation2 (G : Type*) [Magma G] (h518 : Equation518 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h518 X0 X0 X0]
    conv => enter [1]; rw [← h518 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation519 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation519 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ w))))]

@[equational_result]
theorem Equation519_implies_Equation2 (G : Type*) [Magma G] (h519 : Equation519 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h519 X0 X0 X0 X0]
    conv => enter [1]; rw [← h519 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation521 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation521 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ y))))]

theorem Equation521_4512_implies_Equation2 (G : Type*) [Magma G] (h521 : Equation521 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h521 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h521 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [← h521 X2 X0 X1]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l2 X2 X0]
    conv => enter [1]; rw [l4 X2 X2 X0]
  have l6 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l5 X0 (X0 ◇ (X0 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [← h521 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation523 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation523 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ w))))]

@[equational_result]
theorem Equation523_implies_Equation2 (G : Type*) [Magma G] (h523 : Equation523 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h523 X0 X1 X2 X1]
    conv => enter [1]; rw [← h523 X2 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ X0))) X0]
    conv => enter [1]; rw [← h523 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation525 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation525 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ y))))]

@[equational_result]
theorem Equation525_implies_Equation2 (G : Type*) [Magma G] (h525 : Equation525 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h525 X0 X0 X0]
    conv => enter [1]; rw [← h525 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation526 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation526 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ z))))]

@[equational_result]
theorem Equation526_implies_Equation2 (G : Type*) [Magma G] (h526 : Equation526 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h526 X0 X0 X0]
    conv => enter [1]; rw [← h526 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation527 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation527 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ w))))]

@[equational_result]
theorem Equation527_implies_Equation2 (G : Type*) [Magma G] (h527 : Equation527 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h527 X0 X0 X0 X0]
    conv => enter [1]; rw [← h527 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation529 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation529 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ y))))]

@[equational_result]
theorem Equation529_implies_Equation2 (G : Type*) [Magma G] (h529 : Equation529 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h529 X0 X0 X0]
    conv => enter [1]; rw [← h529 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation530 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation530 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ z))))]

@[equational_result]
theorem Equation530_implies_Equation2 (G : Type*) [Magma G] (h530 : Equation530 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h530 X0 X0 X0]
    conv => enter [1]; rw [← h530 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation531 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation531 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ w))))]

@[equational_result]
theorem Equation531_implies_Equation2 (G : Type*) [Magma G] (h531 : Equation531 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h531 X0 X0 X0 X0]
    conv => enter [1]; rw [← h531 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation533 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation533 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ y))))]

@[equational_result]
theorem Equation533_implies_Equation2 (G : Type*) [Magma G] (h533 : Equation533 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h533 X0 X0 X0 X0]
    conv => enter [1]; rw [← h533 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation534 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation534 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ z))))]

@[equational_result]
theorem Equation534_implies_Equation2 (G : Type*) [Magma G] (h534 : Equation534 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h534 X0 X0 X0 X0]
    conv => enter [1]; rw [← h534 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation535 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation535 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ w))))]

@[equational_result]
theorem Equation535_implies_Equation2 (G : Type*) [Magma G] (h535 : Equation535 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h535 X0 X0 X0 X0]
    conv => enter [1]; rw [← h535 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation536 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation536 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ u))))]

@[equational_result]
theorem Equation536_implies_Equation2 (G : Type*) [Magma G] (h536 : Equation536 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h536 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h536 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation538 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation538 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ y))))]

theorem Equation538_4512_implies_Equation2 (G : Type*) [Magma G] (h538 : Equation538 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h538 X0 X1 X0]
    conv => enter [1]; rw [← h538 X0 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h538 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation539 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation539 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ z))))]

theorem Equation539_4512_implies_Equation2 (G : Type*) [Magma G] (h539 : Equation539 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h539 X0 X2 X2]
    conv => enter [1]; rw [← h539 X2 X1 (X0 ◇ (X0 ◇ X2))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h539 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h539 X0 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X2 : G, ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X2]
  have l3 : ∀ X0 X2 : G, (X0 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l2 X0 X2]
  have l4 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [← l1 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [← h539 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation540 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation540 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ w))))]

@[equational_result]
theorem Equation540_implies_Equation2 (G : Type*) [Magma G] (h540 : Equation540 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h540 X0 X3 X3 X1]
    conv => enter [1]; rw [← h540 X3 X1 X2 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h540 X0 X1 X0 X1]
    conv => enter [1]; rw [← h540 X0 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0 X3]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X3 ◇ (X3 ◇ X0))) X0]
    conv => enter [1]; rw [← h540 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation542 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation542 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ y))))]

theorem Equation542_4512_implies_Equation2 (G : Type*) [Magma G] (h542 : Equation542 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h542 (X0 ◇ X0) X0 X1]
    conv => enter [1]; rw [← h542 X1 (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l1 X0 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation544 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation544 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ w))))]

@[equational_result]
theorem Equation544_implies_Equation2 (G : Type*) [Magma G] (h544 : Equation544 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h544 X0 X0 X2 X0]
    conv => enter [1]; rw [← h544 X2 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation547 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation547 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ z))))]

@[equational_result]
theorem Equation547_implies_Equation2 (G : Type*) [Magma G] (h547 : Equation547 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h547 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h547 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h547 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2, 2]; rw [l0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [l0 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h547 X1 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation548 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation548 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ w))))]

@[equational_result]
theorem Equation548_implies_Equation2 (G : Type*) [Magma G] (h548 : Equation548 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h548 X0 X0 X2 X1]
    conv => enter [1]; rw [← h548 X2 X1 X0 (X2 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h548 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation550 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation550 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ y))))]

@[equational_result]
theorem Equation550_implies_Equation2 (G : Type*) [Magma G] (h550 : Equation550 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ X2) ◇ X0) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h550 X0 X2 X3 X1]
    conv => enter [1]; rw [← h550 X3 (X1 ◇ X2) X2 X0]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h550 X4 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation551 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation551 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ z))))]

@[equational_result]
theorem Equation551_implies_Equation2 (G : Type*) [Magma G] (h551 : Equation551 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h551 X0 (X1 ◇ X3) X3 X1]
    conv => enter [1]; rw [← h551 X3 X1 (X1 ◇ X3) X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h551 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation552 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation552 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ w))))]

@[equational_result]
theorem Equation552_implies_Equation2 (G : Type*) [Magma G] (h552 : Equation552 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h552 X0 X3 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h552 X3 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 (X3 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h552 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation553 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation553 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ u))))]

@[equational_result]
theorem Equation553_implies_Equation2 (G : Type*) [Magma G] (h553 : Equation553 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h553 X0 X1 X3 X1 X1]
    conv => enter [1]; rw [← h553 X3 X1 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h553 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation555 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation555 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ y))))]

theorem Equation555_4512_implies_Equation2 (G : Type*) [Magma G] (h555 : Equation555 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h555 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h555 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h555 X0 X2 X1]
    conv => enter [1]; rw [l1 (X1 ◇ (X2 ◇ (X0 ◇ X2))) X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h555 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X2)) X0]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l5 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 (X2 ◇ (X0 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation557 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation557 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ w))))]

@[equational_result]
theorem Equation557_implies_Equation2 (G : Type*) [Magma G] (h557 : Equation557 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h557 X0 X2 X1 X1]
    conv => enter [1]; rw [← h557 X2 X1 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ X0))) X0]
    conv => enter [1]; rw [← h557 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation559 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation559 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation559_implies_Equation2 (G : Type*) [Magma G] (h559 : Equation559 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h559 X0 X0 X0]
    conv => enter [1]; rw [← h559 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation560 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation560 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ z))))]

@[equational_result]
theorem Equation560_implies_Equation2 (G : Type*) [Magma G] (h560 : Equation560 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h560 X0 X0 X0]
    conv => enter [1]; rw [← h560 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation561 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation561 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ w))))]

@[equational_result]
theorem Equation561_implies_Equation2 (G : Type*) [Magma G] (h561 : Equation561 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h561 X0 X0 X0 X0]
    conv => enter [1]; rw [← h561 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation563 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation563 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ y))))]

@[equational_result]
theorem Equation563_implies_Equation2 (G : Type*) [Magma G] (h563 : Equation563 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h563 X0 X0 X0]
    conv => enter [1]; rw [← h563 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation564 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation564 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ z))))]

@[equational_result]
theorem Equation564_implies_Equation2 (G : Type*) [Magma G] (h564 : Equation564 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h564 X0 X0 X0]
    conv => enter [1]; rw [← h564 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation565 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation565 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ w))))]

@[equational_result]
theorem Equation565_implies_Equation2 (G : Type*) [Magma G] (h565 : Equation565 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h565 X0 X0 X0 X0]
    conv => enter [1]; rw [← h565 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation567 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation567 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ y))))]

@[equational_result]
theorem Equation567_implies_Equation2 (G : Type*) [Magma G] (h567 : Equation567 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h567 X0 X0 X0 X0]
    conv => enter [1]; rw [← h567 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation568 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation568 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ z))))]

@[equational_result]
theorem Equation568_implies_Equation2 (G : Type*) [Magma G] (h568 : Equation568 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h568 X0 X0 X0 X0]
    conv => enter [1]; rw [← h568 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation569 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation569 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ w))))]

@[equational_result]
theorem Equation569_implies_Equation2 (G : Type*) [Magma G] (h569 : Equation569 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h569 X0 X0 X0 X0]
    conv => enter [1]; rw [← h569 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation570 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation570 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ u))))]

@[equational_result]
theorem Equation570_implies_Equation2 (G : Type*) [Magma G] (h570 : Equation570 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h570 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h570 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation573 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation573 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ z))))]

theorem Equation573_4512_implies_Equation2 (G : Type*) [Magma G] (h573 : Equation573 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X2)))]
    conv => enter [1]; rw [← h573 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X3 : G, (X0 ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [h573 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X3]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [← h573 X2 X1 X0]
  have l3 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X2]
  have l4 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l3 X0 X2]
  have l5 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l4 X0 X2]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation574 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation574 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ w))))]

@[equational_result]
theorem Equation574_implies_Equation2 (G : Type*) [Magma G] (h574 : Equation574 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h574 X0 X2 X2 X1]
    conv => enter [1]; rw [← h574 X2 X1 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ X0))) X0]
    conv => enter [1]; rw [← h574 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation576 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation576 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ y))))]

@[equational_result]
theorem Equation576_implies_Equation2 (G : Type*) [Magma G] (h576 : Equation576 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h576 X0 X0 X0]
    conv => enter [1]; rw [← h576 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation577 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation577 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ z))))]

@[equational_result]
theorem Equation577_implies_Equation2 (G : Type*) [Magma G] (h577 : Equation577 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h577 X0 X0 X0]
    conv => enter [1]; rw [← h577 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation578 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation578 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ w))))]

@[equational_result]
theorem Equation578_implies_Equation2 (G : Type*) [Magma G] (h578 : Equation578 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h578 X0 X0 X0 X0]
    conv => enter [1]; rw [← h578 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation580 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation580 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ y))))]

@[equational_result]
theorem Equation580_implies_Equation2 (G : Type*) [Magma G] (h580 : Equation580 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h580 X0 X0 X0]
    conv => enter [1]; rw [← h580 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation581 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation581 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ z))))]

@[equational_result]
theorem Equation581_implies_Equation2 (G : Type*) [Magma G] (h581 : Equation581 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h581 X0 X0 X0]
    conv => enter [1]; rw [← h581 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation582 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation582 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ w))))]

@[equational_result]
theorem Equation582_implies_Equation2 (G : Type*) [Magma G] (h582 : Equation582 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h582 X0 X0 X0 X0]
    conv => enter [1]; rw [← h582 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation584 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation584 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ y))))]

@[equational_result]
theorem Equation584_implies_Equation2 (G : Type*) [Magma G] (h584 : Equation584 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h584 X0 X0 X0 X0]
    conv => enter [1]; rw [← h584 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation585 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation585 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ z))))]

@[equational_result]
theorem Equation585_implies_Equation2 (G : Type*) [Magma G] (h585 : Equation585 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h585 X0 X0 X0 X0]
    conv => enter [1]; rw [← h585 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation586 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation586 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ w))))]

@[equational_result]
theorem Equation586_implies_Equation2 (G : Type*) [Magma G] (h586 : Equation586 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h586 X0 X0 X0 X0]
    conv => enter [1]; rw [← h586 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation587 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation587 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ u))))]

@[equational_result]
theorem Equation587_implies_Equation2 (G : Type*) [Magma G] (h587 : Equation587 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h587 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h587 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation589 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation589 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ y))))]

theorem Equation589_4512_implies_Equation2 (G : Type*) [Magma G] (h589 : Equation589 G) (h4512 : Equation4512 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 : G, ((X0 ◇ X1) ◇ X0) = X3 := by
    intro X0 X1 X3
    conv => enter [1, 2]; rw [h589 X0 X1 X0 X3]
    conv => enter [1]; rw [← h589 X3 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X0)) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1 X3]
  have l2 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation590 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation590 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ z))))]

@[equational_result]
theorem Equation590_implies_Equation2 (G : Type*) [Magma G] (h590 : Equation590 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h590 X0 (X0 ◇ X1) X1 X3]
    conv => enter [1]; rw [← h590 X3 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ X0))) X0]
    conv => enter [1]; rw [← h590 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation591 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation591 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ w))))]

@[equational_result]
theorem Equation591_implies_Equation2 (G : Type*) [Magma G] (h591 : Equation591 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h591 X0 X1 (X0 ◇ X3) X3]
    conv => enter [1]; rw [← h591 X3 X1 X1 (X0 ◇ X3)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ X0))) X0]
    conv => enter [1]; rw [← h591 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation592 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation592 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ u))))]

@[equational_result]
theorem Equation592_implies_Equation2 (G : Type*) [Magma G] (h592 : Equation592 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = X4 := by
    intro X1 X0 X4
    conv => enter [1, 2]; rw [h592 X0 X1 X1 X4 X1]
    conv => enter [1]; rw [← h592 X4 X1 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ X0))) X0]
    conv => enter [1]; rw [← h592 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation594 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation594 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ y))))]

@[equational_result]
theorem Equation594_implies_Equation2 (G : Type*) [Magma G] (h594 : Equation594 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h594 X0 X0 X0 X0]
    conv => enter [1]; rw [← h594 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation595 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation595 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ z))))]

@[equational_result]
theorem Equation595_implies_Equation2 (G : Type*) [Magma G] (h595 : Equation595 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h595 X0 X0 X0 X0]
    conv => enter [1]; rw [← h595 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation596 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation596 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ w))))]

@[equational_result]
theorem Equation596_implies_Equation2 (G : Type*) [Magma G] (h596 : Equation596 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h596 X0 X0 X0 X0]
    conv => enter [1]; rw [← h596 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation597 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation597 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ u))))]

@[equational_result]
theorem Equation597_implies_Equation2 (G : Type*) [Magma G] (h597 : Equation597 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h597 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h597 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation599 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation599 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ y))))]

@[equational_result]
theorem Equation599_implies_Equation2 (G : Type*) [Magma G] (h599 : Equation599 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h599 X0 X0 X0 X0]
    conv => enter [1]; rw [← h599 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation600 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation600 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ z))))]

@[equational_result]
theorem Equation600_implies_Equation2 (G : Type*) [Magma G] (h600 : Equation600 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h600 X0 X0 X0 X0]
    conv => enter [1]; rw [← h600 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation601 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation601 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ w))))]

@[equational_result]
theorem Equation601_implies_Equation2 (G : Type*) [Magma G] (h601 : Equation601 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h601 X0 X0 X0 X0]
    conv => enter [1]; rw [← h601 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation602 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation602 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ u))))]

@[equational_result]
theorem Equation602_implies_Equation2 (G : Type*) [Magma G] (h602 : Equation602 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h602 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h602 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation604 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation604 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ y))))]

@[equational_result]
theorem Equation604_implies_Equation2 (G : Type*) [Magma G] (h604 : Equation604 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h604 X0 X0 X0 X0]
    conv => enter [1]; rw [← h604 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation605 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation605 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ z))))]

@[equational_result]
theorem Equation605_implies_Equation2 (G : Type*) [Magma G] (h605 : Equation605 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h605 X0 X0 X0 X0]
    conv => enter [1]; rw [← h605 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation606 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation606 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ w))))]

@[equational_result]
theorem Equation606_implies_Equation2 (G : Type*) [Magma G] (h606 : Equation606 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h606 X0 X0 X0 X0]
    conv => enter [1]; rw [← h606 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation607 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation607 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ u))))]

@[equational_result]
theorem Equation607_implies_Equation2 (G : Type*) [Magma G] (h607 : Equation607 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h607 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h607 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation609 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation609 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ y))))]

@[equational_result]
theorem Equation609_implies_Equation2 (G : Type*) [Magma G] (h609 : Equation609 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h609 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h609 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation610 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation610 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ z))))]

@[equational_result]
theorem Equation610_implies_Equation2 (G : Type*) [Magma G] (h610 : Equation610 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h610 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h610 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation611 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation611 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ w))))]

@[equational_result]
theorem Equation611_implies_Equation2 (G : Type*) [Magma G] (h611 : Equation611 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h611 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h611 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation612 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation612 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ u))))]

@[equational_result]
theorem Equation612_implies_Equation2 (G : Type*) [Magma G] (h612 : Equation612 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h612 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h612 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation613 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation613 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ v))))]

@[equational_result]
theorem Equation613_implies_Equation2 (G : Type*) [Magma G] (h613 : Equation613 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h613 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h613 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation4899 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4899 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_4899_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4899 : Equation4899 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4899 X0 X1]
    conv => enter [1]; rw [← h4899 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4899 X0 X0]
    conv => enter [1]; rw [← h4899 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4899 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h4899 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4899 X1 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation4900 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4900 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation4900_implies_Equation2 (G : Type*) [Magma G] (h4900 : Equation4900 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4900 X0 X2 X1]
    conv => enter [1]; rw [← h4900 X2 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4900 X0 X0 X1]
    conv => enter [1]; rw [← h4900 X0 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 2, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l2 X2 X0]
  have l4 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l3 X2 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4900 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation4902 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4902 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

end Semigroup5
