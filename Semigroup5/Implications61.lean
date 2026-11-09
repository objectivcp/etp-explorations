import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54190_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54190 : Equation54190 G) : Equation54186 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X1 X0 sK1 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro X1 X0 sK1
    conv => enter [1]; rw [h54190 X1 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [← h54190 sK0 X0 (sK1 ◇ sK1)]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54190 X0 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l3 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ sK1) sK1 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l11 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l9 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK1) sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h54190 X0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l6 sK2 sK1]
  have l16 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l15 X0 sK1 sK2]
    conv => enter [1]; rw [l1 X0 (sK2 ◇ (sK1 ◇ sK1)) sK1]
  have l17 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [← l1 X0 sK1 sK1]
    conv => enter [1]; rw [l16 X0 sK1 sK2]
  have l18 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [l17 X0 sK1 sK2]
  have l19 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l11 sK1]
  have l20 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← l19 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) sK1]
  have l21 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l6 sK2 sK1]
    conv => enter [1]; rw [← l20 sK2 sK1]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l21 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l23 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l24 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l23 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l18 (sK0 ◇ (sK1 ◇ sK1)) sK1 sK2]
  have l26 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l18 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) sK1 sK2]
  have l27 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l24 sK0 sK2 sK1 (sK2 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l26 sK0 sK2 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l29 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l27 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK2 ◇ (sK1 ◇ sK1))]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l23 sK0 sK2 sK1]
    conv => enter [1]; rw [← l29 sK0 sK2 sK1]
  have l32 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
  have l33 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l31 sK0 sK2 sK1]
    conv => enter [1]; rw [← l32 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l34 x y z]

@[equational_result]
theorem Equation54190_implies_Equation54162 (G : Type*) [Magma G] (h54190 : Equation54190 G) : Equation54162 G := by
  intro x y
  conv => enter [1]; rw [h54190 x y x]

theorem Equation4512_54190_implies_Equation53812 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54190 : Equation54190 G) : Equation53812 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54190 X1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54190 X0 (sK0 ◇ sK0) sK1]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [← h54190 sK0 sK0 sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54190 sK1 sK0 sK0]
    conv => enter [1]; rw [← l0 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54190 sK1 sK0 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  have l7 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h54190 X0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l5 sK1 sK0]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l7 X0 sK0 sK1]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l8 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h54190 X0 (sK1 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK0 sK1]
  have l11 : ∀ X0 sK1 sK0 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l10 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l1 sK1 sK0]
  have l12 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l11 X0 sK1 sK0]
  have l13 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l12 X0 sK1 sK0]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l14 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l13 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l9 X0 sK0 sK1]
    conv => enter [1]; rw [← l14 X0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x x y]

@[equational_result]
theorem Equation54190_implies_Equation53815 (G : Type*) [Magma G] (h54190 : Equation54190 G) : Equation53815 G := by
  intro x y
  conv => enter [1]; rw [h54190 x x y]

theorem Equation4512_53888_implies_Equation53866 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53888 : Equation53888 G) : Equation53866 G := by
  have l0 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h53888 sK0 X0 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ X0)]
    conv => enter [1]; rw [← h53888 sK2 X0 sK1]
  have l2 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [← h53888 X0 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [h53888 X0 (sK2 ◇ sK1) X1]
  have l3 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h53888 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l5 : ∀ X0 sK0 sK2 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK2 sK1 X1
    conv => enter [1]; rw [l2 X0 sK0 sK2 sK1 X1]
    conv => enter [1, 2]; rw [h53888 X1 (sK2 ◇ sK1) sK0]
  have l6 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ sK1) sK2 sK1]
    conv => enter [1]; rw [l4 sK0 sK2 sK1]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h53888 sK0 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [l6 sK0 sK2 sK1]
  have l8 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h53888 sK0 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X1 ◇ sK1))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h53888 X0 sK1 sK0]
    conv => enter [1]; rw [h53888 X0 sK1 X1]
  have l10 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [h53888 (sK0 ◇ (sK2 ◇ sK1)) sK1 sK0]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l10 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l9 X0 sK0 sK1 X1]
    conv => enter [1, 2]; rw [h53888 X1 sK1 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53888 sK0 sK1 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53888 sK0 sK1 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l16 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h53888 sK2 (sK2 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [h53888 sK2 sK1 sK0]
  have l17 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h53888 sK2 sK1 sK0]
  have l18 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l17 sK2 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l19 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK0 sK1]
    conv => enter [1]; rw [← l1 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l12 (sK2 ◇ sK1) sK0 sK1 sK1]
    conv => enter [1]; rw [← l19 sK2 sK0 sK1]
  have l21 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [h53888 X0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK2]
    conv => enter [1, 2, 2]; rw [← l20 sK2 sK1 sK0]
  have l22 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l21 X0 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [l18 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l23 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l22 X0 sK0 sK2 sK1]
    conv => enter [1, 2]; rw [← l12 sK2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l12 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 X0 sK0 sK2 sK1]
  have l25 : ∀ X0 sK0 sK2 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK2 sK1
    conv => enter [1]; rw [l5 X0 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l24 X0 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l8 sK0 sK2 sK1]
    conv => enter [1]; rw [l25 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK0 sK2 sK1]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l27 x y z]

theorem Equation4512_53888_implies_Equation53873 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53888 : Equation53888 G) : Equation53873 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l3 sK1 X0]
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
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l7 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK0 sK1 ((sK1 ◇ sK1) ◇ X0)]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1]; rw [← h53888 sK0 X0 (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l14 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53888 sK1 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← l14 sK1 X0]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l17 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l16 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1]
  have l18 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l17 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l20 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 (sK1 ◇ sK1)]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation4512_53888_implies_Equation53809 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53888 : Equation53888 G) : Equation53809 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l7 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l11 sK1 sK0 (sK0 ◇ X0)]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK0 X0]
    conv => enter [1]; rw [← h53888 (sK1 ◇ sK0) X0 sK0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [l14 sK1 sK0 X0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [← h53888 X1 X0 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53888 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l18 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53888 sK0 X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l19 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK1 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h53888 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X1 ◇ (X1 ◇ X0))]
  have l20 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53888 (sK0 ◇ sK0) X0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l6 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l21 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 2]; rw [h53888 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (X1 ◇ (X1 ◇ X0))]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [← h53888 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0 sK0]
  have l23 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l4 sK0 X0]
    conv => enter [1]; rw [l20 sK0 X0 sK1]
  have l24 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0 sK1]
    conv => enter [1]; rw [← h53888 (sK1 ◇ sK0) X0 sK1]
  have l25 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l18 sK0 X0 sK1]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
    conv => enter [1]; rw [← l22 sK0 sK1 X0]
  have l28 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ X0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l24 sK1 sK0 X0]
    conv => enter [1]; rw [← l15 sK1 sK0 X0]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l31 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l28 sK1 sK0 X0]
  have l32 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l25 sK0 X0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 X0]
  have l33 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0 sK0]
    conv => enter [1]; rw [← l7 sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l33 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l39 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l38 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53888 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l38 sK0]
  have l44 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l38 sK0]
    conv => enter [1]; rw [← l43 X0 sK0]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l46 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l41 sK1 sK0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l49 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53888 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l45 sK1 sK0]
  have l50 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l49 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l15 sK1 sK0 (sK0 ◇ sK0)]
  have l51 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l50 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l31 sK1 sK0 (sK0 ◇ sK0)]
  have l52 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l51 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l45 sK1 sK0]
  have l53 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l44 X0 sK0]
    conv => enter [1]; rw [l52 X0 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h53888 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l6 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h53888 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l60 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l62 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1]
  have l67 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l68 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l67 sK0 sK1 X0]
    conv => enter [1]; rw [← l16 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 X0]
  have l69 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l32 sK0 X0 sK1]
    conv => enter [1]; rw [← l68 sK0 sK1 X0]
  have l70 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53888 sK1 sK0 sK0]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53888 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l70 sK1 sK0]
  have l72 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0 sK1]
    conv => enter [1]; rw [← l71 sK1 sK0]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l72 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
  have l74 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l73 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l74 sK1 sK0]
  have l76 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ sK0)]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← l76 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l77 sK0 sK1]
  have l79 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0]
    conv => enter [1]; rw [← l78 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l79 x y]

theorem Equation4512_53888_implies_Equation53815 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53888 : Equation53888 G) : Equation53815 G := by
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
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
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
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l8 sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l11 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l15 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l14 sK1 sK0 X0]
    conv => enter [1]; rw [← h53888 sK1 X0 (sK0 ◇ sK0)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l15 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) X0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53888 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53888 sK0 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l22 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h53888 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l12 sK1 sK0 (X1 ◇ (X1 ◇ X0))]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h53888 (sK0 ◇ (sK0 ◇ sK0)) X0 sK1]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 X0]
  have l25 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h53888 sK1 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l23 sK1 sK0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l24 sK0 X0]
  have l28 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l26 sK1 X0 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l29 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l28 sK1 X0 sK0]
    conv => enter [1, 2]; rw [l10 sK0 X0]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0]
    conv => enter [1]; rw [← l29 sK1 X0 sK0]
  have l31 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0]
    conv => enter [1]; rw [← l6 sK0]
  have l32 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l32 sK0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l31 sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [l11 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53888 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2, 2]; rw [← l34 sK0]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l34 sK0]
    conv => enter [1]; rw [← l37 X0 sK0]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [← l35 sK1 sK0]
  have l40 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l41 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l36 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1, 2]; rw [← l41 sK1 sK0]
  have l43 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53888 X0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK0]
  have l44 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l38 X0 sK0]
    conv => enter [1]; rw [l43 X0 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l40 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l40 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [← h53888 sK0 (sK1 ◇ sK0) sK1]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 (sK0 ◇ sK0) sK0 sK1]
    conv => enter [1]; rw [← l45 sK0 sK1]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l48 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1, 2]; rw [l49 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l52 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 (sK1 ◇ sK0)]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [l53 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK0)]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1, 2]; rw [← l27 sK0 (sK1 ◇ sK0)]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l27 sK0 (sK1 ◇ sK0)]
  have l59 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l54 sK0 sK0]
    conv => enter [1]; rw [← l58 sK0 sK0]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l61 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l60 sK1 sK0]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [← l61 sK1 sK0]
  have l63 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0 (sK0 ◇ sK0)]
  have l64 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [l63 sK1 sK0]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l64 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l42 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [← h53888 sK0 (sK1 ◇ sK0) sK1]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← l69 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l70 x y]

theorem Equation4512_54181_implies_Equation4270 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation4270 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54181 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54181_implies_Equation54179 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation54179 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54181 X0 X1 X0]
    conv => enter [1]; rw [← h54181 X0 X3 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54181 sK1 X0 sK1]
  have l3 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54181 sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK1 ◇ sK1)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l2 sK1 X0]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1]; rw [l3 sK1 sK1 sK2]
  have l6 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK2]
  have l7 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l7 sK1 sK2]
  have l9 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← l8 sK1 sK2 X0]
  have l10 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l12 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK2]
    conv => enter [1]; rw [← l3 sK1 sK1 sK2]
  have l13 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l3 sK1 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l13 sK1 X0 sK1]
    conv => enter [1]; rw [← l9 sK1 X0 sK1]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1]; rw [← l14 sK1 X0]
  have l16 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l17 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l18 sK1 sK2]
  have l20 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ sK1) sK2]
  have l21 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← l20 sK1 sK2]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l21 sK1 sK2]
  have l23 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
  have l24 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← l16 sK1 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [l24 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK2)) (sK1 ◇ (sK2 ◇ sK2))]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

theorem Equation4512_54181_implies_Equation54190 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation54190 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54181 X0 X1 X0]
    conv => enter [1]; rw [← h54181 X0 X3 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X3)) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h54181 X2 X3 X0]
    conv => enter [1, 2]; rw [l0 X0 X2 X1]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X0 ◇ ((X2 ◇ X2) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ X2) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X3) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X2 X2 X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X3)) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X3]
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
  have l5 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1, 2]; rw [h4512 X1 X1 X3]
    conv => enter [1]; rw [l4 X0 X1 X3 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y y y]
  conv => enter [1]; rw [l5 x y y z]

theorem Equation4512_54181_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation54176 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK2]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l3 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54181 X0 X1 X0]
    conv => enter [1]; rw [← h54181 X0 X3 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54181 sK1 X0 sK1]
  have l5 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h54181 sK1 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK1)]
  have l6 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK1]
    conv => enter [1]; rw [l4 sK1 X0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l6 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK2]
  have l8 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l9 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l8 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK1)]
  have l11 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK0 sK1 sK2]
  have l12 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l11 sK0 sK1 sK2]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK2) sK2]
  have l15 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK1 X0 sK2]
  have l16 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l15 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l9 sK1 sK1]
  have l17 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [← l14 sK1 sK2]
  have l18 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l16 sK1 X0]
    conv => enter [1]; rw [l5 sK1 (sK1 ◇ sK1) sK2]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l9 sK1 sK1]
    conv => enter [1]; rw [← l18 sK1 X0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l5 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK1)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X0)]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l23 sK0 sK1 X0]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ sK1) X0]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1 X0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [← l27 sK0 sK1 sK0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l32 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
  have l33 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l36 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l31 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
  have l38 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1 sK2]
    conv => enter [1]; rw [← l36 sK0 sK1 sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l33 sK0 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l17 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l39 sK0 sK1 sK2]
    conv => enter [1]; rw [l13 sK0 sK1 sK2 (sK1 ◇ sK1)]
  have l41 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l25 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← l41 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l43 x y z]

@[equational_result]
theorem Equation54181_implies_Equation54171 (G : Type*) [Magma G] (h54181 : Equation54181 G) : Equation54171 G := by
  intro x y
  conv => enter [1]; rw [h54181 x y y]

theorem Equation4512_54181_implies_Equation53817 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation53817 G := by
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
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54181 sK0 X0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54181 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54181 sK0 X0 sK0]
  have l8 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h54181 sK0 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 sK2]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l18 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0 sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l25 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l25 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l28 : ∀ sK0 X0 sK1 sK2 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l29 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l28 sK0 X0 sK1 sK2]
  have l30 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [l29 sK0 X0 sK1 sK2]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l18 sK0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l26 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l31 sK0]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1]; rw [← l33 sK0 X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54181 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 X0]
  have l38 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← l12 sK0 X0]
  have l39 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l38 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l37 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l34 sK0]
  have l41 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l39 sK0 X0 X1]
    conv => enter [1]; rw [← l36 sK0 X1]
  have l42 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l41 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l43 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ (X2 ◇ X2)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h54181 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l8 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l43 sK0 sK0 X0 X1]
  have l45 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 sK0 sK0]
    conv => enter [1]; rw [l44 sK0 sK0 sK0 X0 X1]
  have l46 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [l45 sK0 X0 X1]
  have l47 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l46 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ (sK0 ◇ sK0))]
  have l48 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54181 X1 X2 X0]
    conv => enter [1, 2]; rw [l40 X0 X1 sK0]
  have l49 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1]; rw [l40 sK1 sK2 sK0]
  have l50 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l40 X1 X1 sK0]
    conv => enter [1]; rw [l48 X1 X1 X0 sK0]
  have l51 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l50 X1 sK0 X0]
    conv => enter [1, 2]; rw [← l40 X0 sK0 sK0]
  have l52 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l40 X1 sK0 sK0]
    conv => enter [1]; rw [l51 X1 sK0 X0]
  have l53 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [l49 sK1 sK2 sK0]
  have l54 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l53 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l40 sK1 sK0 sK0]
  have l55 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l54 sK1 sK2 sK0]
    conv => enter [1]; rw [← l52 sK1 sK0 sK1]
  have l56 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l30 sK0 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [l55 sK1 sK2 sK0]
  have l57 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l47 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [← l56 sK0 sK2 sK0]
  have l58 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l57 sK0 sK2]
    conv => enter [1]; rw [l42 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l58 x y z]

theorem Equation4512_54181_implies_Equation53820 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation53820 G := by
  have l0 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (X3 ◇ X3)) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h54181 X0 X1 X0]
    conv => enter [1]; rw [← h54181 X0 X3 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54181 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← h54181 sK0 X0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54181 sK0 sK0 X0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54181 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [l5 X0 sK0 sK0]
  have l7 : ∀ X0 sK2 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l0 X0 sK2 X0]
    conv => enter [1]; rw [l5 X0 X0 sK0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l8 x y z]

theorem Equation4512_54181_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54181 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54181 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_54181_implies_Equation53816 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation53816 G := by
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
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l3 sK1 X0]
  have l5 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l5 sK1]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l5 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l8 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← h54181 sK0 X0 (sK0 ◇ sK0)]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h54181 sK1 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l8 sK1 sK1]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h54181 sK0 X0 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h54181 sK1 X0 sK1]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 sK1]
    conv => enter [1]; rw [l12 sK1 X0]
  have l14 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
    conv => enter [1]; rw [← l10 sK1 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l16 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l5 sK1]
    conv => enter [1]; rw [l14 sK1 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1]
    conv => enter [1]; rw [← l17 sK1 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l21 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l19 sK1]
    conv => enter [1]; rw [← l4 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l11 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l24 sK0 sK1]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0 sK0]
    conv => enter [1]; rw [← l20 sK0 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l16 sK1 sK1]
  have l32 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l31 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l32 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l34 x y]

theorem Equation4512_54181_implies_Equation53808 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54181 : Equation54181 G) : Equation53808 G := by
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
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK1]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54181 sK0 X0 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h54181 sK0 (sK0 ◇ sK0) X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54181 sK0 sK0 X0]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h54181 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54181 sK0 X0 (sK0 ◇ sK0)]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0 sK0]
    conv => enter [1]; rw [← l14 sK0 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l7 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l22 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1]; rw [← l32 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l33 x y]

theorem Equation4512_53913_implies_Equation4275 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation4275 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_53913_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53888 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h53913 sK2 sK1 sK2]
    conv => enter [1]; rw [← h53913 X0 sK1 sK2]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h53913 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l1 sK0 sK2 sK1]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h53913 sK2 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
  have l5 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_53913_implies_Equation53968 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53968 G := by
  have l0 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK2)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53913 X0 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK1) sK2]
  have l1 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK2) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) sK2]
  have l2 : ∀ X0 sK2 X1 sK0 sK1 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = (((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK0 sK1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l1 X0 sK2 sK0 sK1]
  have l3 : ∀ X0 sK2 X1 sK0 sK1 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ X1)) := by
    intro X0 sK2 X1 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK2 X1 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2 X1]
  have l4 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [← l3 X0 sK2 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h53913 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← h53913 X0 (sK0 ◇ sK1) sK0]
  have l6 : ∀ sK2 sK0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [h53913 sK2 (sK0 ◇ sK1) X1]
  have l7 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l5 (sK0 ◇ sK1) sK0 sK1 sK2]
  have l8 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK0 ◇ sK1)) X1]
  have l9 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l5 (sK0 ◇ sK1) sK0 sK1 sK2]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK1)) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l5 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  have l11 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l8 sK2 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK0 sK1 sK2]
  have l13 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [l5 sK0 sK0 sK1 sK2]
  have l14 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l12 sK2 sK0 sK1]
  have l15 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l16 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l6 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) X1]
  have l17 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1)) X1]
  have l18 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1)))) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1]; rw [l17 sK2 sK0 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l19 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l9 sK2 sK0 sK1]
  have l20 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l19 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))]
  have l21 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l20 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l22 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l18 sK2 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l21 X0 sK0 sK1 sK2]
  have l23 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l22 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l24 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l10 sK2 sK0 sK1]
    conv => enter [1]; rw [l15 sK2 sK0 sK1 ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l10 sK2 sK0 sK1]
  have l25 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l15 sK2 sK0 sK1 (sK0 ◇ sK1)]
  have l26 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l25 sK2 sK0 sK1]
    conv => enter [1]; rw [← l15 sK2 sK0 sK1 (sK0 ◇ sK1)]
  have l27 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l26 sK2 sK0 sK1]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h53913 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [l15 sK2 sK0 sK1 ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h53913 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) sK2]
  have l29 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))))) = (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53913 X1 ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h53913 X0 (sK0 ◇ sK1) sK2]
  have l30 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l29 X1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))))]
  have l31 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l32 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK1))))))) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l30 X1 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))]
  have l33 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l6 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l5 sK2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l32 X1 sK0 sK1 sK2 sK0]
  have l35 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK0]
  have l36 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l33 sK2 sK0 sK1]
    conv => enter [1]; rw [← l35 sK0 sK1 sK2]
  have l37 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l36 sK2 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [l14 sK2 sK0 sK1]
  have l38 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l37 sK2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l24 sK2 sK0 sK1]
  have l39 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l27 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0]
  have l40 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l38 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))]
  have l41 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l40 sK2 sK0 sK1]
    conv => enter [1]; rw [← l4 sK2 sK0 sK1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK2 ◇ (sK0 ◇ sK1))]
  have l42 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK2]
    conv => enter [1, 2]; rw [← l41 sK2 sK0 sK1]
  have l43 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l42 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [l23 sK2 sK0 sK1]
  have l44 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l26 sK2 sK0 sK1]
    conv => enter [1]; rw [← l43 X0 sK2 sK0 sK1]
  have l45 : ∀ sK2 sK0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l44 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [h53913 sK2 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) X1]
  have l46 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) = ((X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ ((X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) X1]
    conv => enter [1, 2, 2]; rw [← l44 sK2 sK0 sK1 X1]
  have l47 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l44 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l48 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l47 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l49 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l46 X0 X1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 X1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ((X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l50 : ∀ sK2 sK0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l45 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [← l39 sK2 sK0 sK1 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
  have l51 : ∀ X0 X1 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) = (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X1 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))))) := by
    intro X0 X1 sK2 sK0 sK1
    conv => enter [1]; rw [l49 X0 X1 sK2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l52 : ∀ sK2 sK0 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l48 sK2 sK0 sK1 X1 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l51 X0 X1 sK2 sK0 sK1]
  have l53 : ∀ X1 sK2 sK0 sK1 X0 : G, (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro X1 sK2 sK0 sK1 X0
    conv => enter [1, 2]; rw [l50 sK2 sK0 sK1 (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))]
    conv => enter [1]; rw [← l49 X0 X1 sK2 sK0 sK1]
  have l54 : ∀ sK2 sK0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X1
    conv => enter [1]; rw [l52 sK2 sK0 sK1 sK2 X1]
    conv => enter [1]; rw [← l53 X1 sK2 sK0 sK1 sK2]
  have l55 : ∀ sK2 sK0 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro sK2 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l54 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) X1]
  have l56 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1, 2]; rw [l55 sK2 sK0 sK1 X0 X0]
    conv => enter [1]; rw [← h53913 X1 X0 (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l57 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l55 sK2 sK0 sK1 X0 X0]
    conv => enter [1]; rw [l56 X0 sK2 sK0 sK1 X1]
  have l58 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 sK1 (X0 ◇ (X0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l57 X0 sK0 sK1 sK1 sK0]
  have l59 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l58 X0 sK1 sK0]
    conv => enter [1]; rw [l13 sK1 sK0 sK1 sK2]
  have l60 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l44 sK2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l59 X0 sK1 sK0 sK2]
  have l61 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l60 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l57 sK2 sK0 sK1 sK1 sK2]
  have l62 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l57 sK2 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [← l61 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l62 x y z]

theorem Equation4512_53913_implies_Equation53934 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53934 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53913 X0 X1 X0]
    conv => enter [1]; rw [← h53913 X2 X1 X0]
  have l1 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [h53913 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l2 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [← h53913 sK2 (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l3 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ (sK0 ◇ sK1)) sK0 sK1 sK2]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK1 sK2]
  have l5 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h53913 sK2 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53913 sK0 sK1 sK0]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 sK1 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK1 sK2]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l11 X0 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1 sK0]
    conv => enter [1]; rw [l4 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l10 sK0 sK1 sK0]
  have l14 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 2]; rw [l10 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l15 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l0 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l15 sK2 sK0 sK1]
  have l17 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK0]
    conv => enter [1]; rw [l16 sK0 sK0 sK1 sK2]
  have l18 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l17 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l20 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l19 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [← l18 X0 sK2 sK0 sK1]
  have l21 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l14 sK2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l21 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l22 x y z]

@[equational_result]
theorem Equation53913_implies_Equation53907 (G : Type*) [Magma G] (h53913 : Equation53913 G) : Equation53907 G := by
  intro x y
  conv => enter [1]; rw [h53913 x y x]

theorem Equation4512_53913_implies_Equation53850 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53850 G := by
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
  have l5 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l6 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53913 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l10 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK0) ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h53913 X0 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 sK2]
  have l11 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l10 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) sK2]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l18 sK0 X0]
  have l20 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = (((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2) ◇ X1) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l11 X0 sK2 sK0]
  have l21 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ sK2) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l11 sK0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK2]
  have l22 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X1)) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [l20 X0 sK2 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK0)) sK2 X1]
  have l23 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X1)) = (X0 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [← l22 X0 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l24 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) = (((sK0 ◇ sK0) ◇ sK2) ◇ X0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK2 ◇ sK0)) sK2 X0]
    conv => enter [1, 1]; rw [l21 sK2 sK0]
  have l25 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l24 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK2 X0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l27 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [h53913 sK0 sK0 X1]
  have l28 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l29 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l15 sK0 sK0]
  have l30 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ sK0) ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l15 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) ((sK2 ◇ sK0) ◇ sK0)]
  have l31 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l30 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 sK0]
  have l32 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l29 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l33 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l28 sK0]
  have l34 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l27 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l35 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l31 sK2 sK0]
    conv => enter [1]; rw [l25 sK2 sK0 (sK0 ◇ sK0)]
  have l36 : ∀ sK2 sK0 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← l5 sK2 sK0 sK0]
    conv => enter [1]; rw [l32 sK2 sK0]
  have l37 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l34 sK0 X1]
  have l38 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l15 sK0 sK2]
  have l39 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l35 sK2 sK0]
  have l40 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK2 sK0]
  have l41 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l21 sK2 sK0]
    conv => enter [1, 1]; rw [← l38 sK0 sK2]
  have l42 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h53913 (X0 ◇ X1) (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l43 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l42 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK2 ◇ (sK2 ◇ sK0))]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53913 sK1 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← l38 sK0 sK2]
    conv => enter [1, 2, 1]; rw [← l38 sK0 sK2]
  have l45 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 2, 1]; rw [l38 sK0 sK2]
    conv => enter [1, 1]; rw [l38 sK0 sK2]
    conv => enter [1]; rw [l43 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l38 sK0 sK2]
  have l46 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l44 sK1 sK2 sK0]
    conv => enter [1]; rw [← l19 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l47 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [l45 sK0 sK1 sK2 X0 X1]
  have l48 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l46 sK1 sK2 sK0]
    conv => enter [1]; rw [l47 sK0 sK1 sK2 X0 X1]
  have l49 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l37 sK0 (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK0 sK0]
  have l50 : ∀ sK0 sK2 X0 : G, (((sK0 ◇ sK0) ◇ sK2) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l41 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK2 X0]
  have l51 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1]; rw [l50 sK0 sK2 X0]
  have l52 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l49 sK0 sK2]
    conv => enter [1]; rw [l6 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l49 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 (sK0 ◇ sK0) sK0]
  have l54 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h53913 X0 (sK2 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l49 sK0 sK2]
  have l55 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l54 X0 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l56 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l53 sK0 X0]
  have l57 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l52 sK2 sK0]
    conv => enter [1, 2]; rw [← l51 sK0 sK2 (sK0 ◇ sK0)]
  have l58 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l55 X0 sK2 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l59 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l56 sK0 X0]
  have l60 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l57 sK2 sK0]
    conv => enter [1, 2]; rw [← l39 sK2 sK0]
  have l61 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l58 X0 sK2 sK0]
    conv => enter [1]; rw [← l48 sK1 sK2 sK0 sK2 (sK0 ◇ sK0)]
  have l62 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l60 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l63 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [l61 sK2 sK2 sK0 sK1]
  have l64 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l62 sK2 sK0]
    conv => enter [1, 1]; rw [← l38 sK0 sK2]
  have l65 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l25 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l63 sK2 sK0 sK1]
  have l66 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l64 sK2 sK0]
  have l67 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l39 sK2 sK0]
    conv => enter [1]; rw [l65 sK0 sK2 sK1]
  have l68 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l66 sK0 sK2]
    conv => enter [1]; rw [← l40 sK2 sK0]
  have l69 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l40 sK2 sK0]
    conv => enter [1]; rw [l67 sK2 sK0 sK1]
  have l70 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l68 sK0 sK2]
  have l71 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l70 sK0 sK2]
  have l72 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l59 sK0 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK2 ◇ sK0)) ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l73 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l72 sK1 sK0 sK2]
    conv => enter [1, 2, 1]; rw [← l38 sK0 sK2]
  have l74 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l73 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l4 sK0]
  have l75 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l74 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l26 sK0]
  have l76 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l75 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [← l33 sK0]
  have l77 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l38 sK0 sK2]
    conv => enter [1]; rw [l76 sK1 sK0 sK2]
  have l78 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1, 2, 2]; rw [← l69 sK2 sK0 sK1]
  have l79 : ∀ sK2 sK0 X0 sK1 : G, ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l78 X0 sK1 sK2 sK0]
  have l80 : ∀ sK0 sK2 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [← l25 sK2 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l79 sK2 sK0 X0 sK1]
  have l81 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [l71 sK0 sK2]
    conv => enter [1]; rw [l80 sK0 sK2 X0 sK1]
  have l82 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l81 sK0 X0 sK1 sK2]
  have l83 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l33 sK0]
    conv => enter [1]; rw [l82 sK0 X0 sK1 sK2]
  have l84 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [l83 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1 sK2]
    conv => enter [1]; rw [← h53913 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l85 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l83 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l84 sK1 sK2 sK0 sK0]
  have l86 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l85 sK0 sK1 sK2]
    conv => enter [1]; rw [← l77 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l86 x y z]

theorem Equation4512_53913_implies_Equation53838 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53838 G := by
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
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53913 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l4 X0 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l3 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ X0 sK0 X1 : G, (X0 ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l9 sK0 X0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l9 sK0 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0]
  have l16 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) = (X0 ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1]; rw [← l13 X0 sK0 X1]
  have l17 : ∀ X0 sK0 X1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ X1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 X0 sK0 X1]
    conv => enter [1]; rw [← l16 sK0 X1 X0]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l15 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h53913 X0 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2, 2]; rw [← l9 sK0 sK2]
  have l20 : ∀ sK0 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l17 (sK2 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l19 X0 sK2 sK0]
  have l21 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l18 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 X0 sK2]
  have l22 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l21 sK0 X0 sK2]
  have l23 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l22 sK0 X0 sK2]
  have l24 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l23 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation4512_53913_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53832 G := by
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
  have l3 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l8 sK0 sK0]
    conv => enter [1]; rw [h53913 sK0 sK0 X1]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l8 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0]
  have l12 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l9 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l13 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l12 sK0 X1]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l11 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l11 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l13 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (X0 ◇ sK0)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l16 sK0 X0]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [l18 sK1 sK0]
  have l20 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l19 sK1 sK0]
  have l21 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l20 X0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l21 X0 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l22 X0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l23 x y]

theorem Equation4512_53913_implies_Equation53835 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53835 G := by
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
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53913 X0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l2 sK0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l10 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l11 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l10 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l8 X0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l7 sK0 X0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l13 sK0 X0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l18 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = (((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) ◇ X1) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [l11 X0 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ sK1) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
  have l20 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X1)) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l18 X0 sK1 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 X1]
  have l21 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X1)) = (X0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l20 X0 sK1 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l22 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1 X0]
    conv => enter [1, 1]; rw [l19 sK1 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l22 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l24 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l25 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X1
    conv => enter [1]; rw [l15 sK0 sK0]
    conv => enter [1]; rw [h53913 sK0 sK0 X1]
  have l26 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l15 sK0 sK0]
  have l27 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l15 sK0 sK0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l29 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l26 sK0]
  have l30 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l25 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ sK0)]
  have l31 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 sK0]
    conv => enter [1]; rw [l28 sK1 sK0]
  have l33 : ∀ sK0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l30 sK0 X1]
  have l34 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l31 sK0]
    conv => enter [1, 2]; rw [← l17 sK0]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l32 sK1 sK0]
  have l37 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l38 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l37 sK0]
  have l39 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2, 1]; rw [← l35 sK0 sK1]
  have l40 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l38 sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l40 sK0]
    conv => enter [1]; rw [l6 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l41 sK1 sK0]
    conv => enter [1]; rw [← l39 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l43 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l36 sK1 sK0]
    conv => enter [1]; rw [l42 sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l35 sK0 sK1]
    conv => enter [1]; rw [l43 sK1 sK0]
  have l45 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l46 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l45 sK0 sK1]
  have l47 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l48 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l47 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l49 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l46 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l50 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l49 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l51 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l50 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l48 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l52 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l51 X0 sK1 sK0]
    conv => enter [1]; rw [← l39 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l52 X0 sK1 sK0]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0 sK1]
    conv => enter [1]; rw [← l21 sK1 sK0 (sK0 ◇ sK0) sK1]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [l23 sK1 sK0 (sK0 ◇ sK0)]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK1]
    conv => enter [1]; rw [← l55 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l56 x y]

theorem Equation4512_53913_implies_Equation53822 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53822 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK1 sK0]
  have l9 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l7 sK1 sK0]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l9 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l16 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation54188_implies_Equation54180 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54180 G := by
  have l0 : ∀ X1 X2 X0 sK2 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X2 X0 sK2
    conv => enter [1]; rw [h54188 X1 X2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54188 X0 sK2 X2 sK2]
  have l1 : ∀ X1 X2 sK2 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l0 X1 X2 X1 sK2]
    conv => enter [1]; rw [← h54188 X1 sK2 X1 sK2]
  have l2 : ∀ X0 sK2 X1 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK2 X1 sK3 sK0
    conv => enter [1]; rw [l1 X0 sK2 sK3]
    conv => enter [1]; rw [h54188 X0 sK3 X1 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y y z w]

@[equational_result]
theorem Equation54188_implies_Equation54194 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54194 G := by
  have l0 : ∀ X1 X2 X0 sK2 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X2 X0 sK2
    conv => enter [1]; rw [h54188 X1 X2 X0 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h54188 X0 sK2 X2 sK2]
  have l1 : ∀ X1 X2 sK2 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X1 X2 sK2
    conv => enter [1]; rw [l0 X1 X2 X1 sK2]
    conv => enter [1]; rw [← h54188 X1 sK2 X1 sK2]
  have l2 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [l1 X0 sK2 sK0]
    conv => enter [1]; rw [h54188 X0 sK0 sK3 sK2]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation54188_implies_Equation54184 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54184 G := by
  have l0 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [h54188 X1 X2 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h54188 X0 sK0 X2 sK0]
  have l1 : ∀ X1 X2 sK0 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l0 X1 X2 X1 sK0]
    conv => enter [1]; rw [← h54188 X1 sK0 X1 sK0]
  have l2 : ∀ X0 sK0 sK2 sK1 sK3 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK3))) := by
    intro X0 sK0 sK2 sK1 sK3
    conv => enter [1]; rw [l1 X0 sK0 sK1]
    conv => enter [1]; rw [h54188 X0 sK1 sK2 sK3]
  intro x y z w
  conv => enter [1]; rw [l2 x y z x w]

@[equational_result]
theorem Equation54188_implies_Equation54187 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54187 G := by
  intro x y z
  conv => enter [1]; rw [h54188 x y z z]

@[equational_result]
theorem Equation54188_implies_Equation54185 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54185 G := by
  intro x y z
  conv => enter [1]; rw [h54188 x y z x]

@[equational_result]
theorem Equation54188_implies_Equation54177 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54177 G := by
  have l0 : ∀ X1 X2 X0 sK1 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X1 X2 X0 sK1
    conv => enter [1]; rw [h54188 X1 X2 X0 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h54188 X0 sK1 X2 sK1]
  have l1 : ∀ X1 X2 sK1 : G, (X1 ◇ (X2 ◇ X2)) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X1 X2 sK1
    conv => enter [1]; rw [l0 X1 X2 X1 sK1]
    conv => enter [1]; rw [← h54188 X1 sK1 X1 sK1]
  have l2 : ∀ X0 sK1 X1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 X1 sK2 sK0
    conv => enter [1]; rw [l1 X0 sK1 sK2]
    conv => enter [1]; rw [h54188 X0 sK2 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y y z x]

theorem Equation4512_54188_implies_Equation53821 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54188 : Equation54188 G) : Equation53821 G := by
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
  have l4 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l5 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l6 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK2 ◇ (sK3 ◇ sK0))]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l9 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l1 sK1 X0]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ X0)]
  have l11 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← l3 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1]; rw [← h54188 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54188 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [← l10 sK1 X0]
  have l14 : ∀ sK1 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [h54188 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1]; rw [l12 sK1 sK1]
  have l15 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l13 sK1 X0]
  have l16 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l14 sK1]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l15 sK1 X0]
  have l18 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← l9 sK1]
    conv => enter [1]; rw [l16 sK1]
  have l19 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l17 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l18 sK1]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l19 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l21 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 X0]
    conv => enter [1]; rw [← l20 sK1 X0]
  have l22 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l23 : ∀ sK1 X0 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l22 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0]
  have l24 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1]; rw [l23 sK1 X0 sK2 sK3 sK0]
  have l25 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l3 sK1 ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK3 sK0 X0]
  have l26 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h54188 (sK1 ◇ sK1) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK1 X0]
    conv => enter [1]; rw [← l25 sK1 sK2 sK3 sK0 X0]
  have l27 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l26 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← h54188 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK1 ◇ sK1)) sK1]
  have l28 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK2 ◇ (sK3 ◇ sK0))]
  have l29 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK3 sK0 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [l28 sK1 sK2 sK3 sK0]
  have l30 : ∀ sK1 X0 sK2 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 1]; rw [l29 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK2 ◇ (sK3 ◇ sK0)) X0]
  have l31 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l21 sK1 X0]
    conv => enter [1]; rw [l30 sK1 X0 sK2 sK3 sK0]
  have l32 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54188 X0 X1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l21 sK1 (X1 ◇ X0)]
  have l33 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l31 sK1 sK2 sK3 sK0 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h54188 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) X0 (sK2 ◇ (sK3 ◇ sK0)) sK1]
  have l34 : ∀ X0 X1 sK3 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 X1 sK3 sK0 sK1
    conv => enter [1]; rw [← h54188 X0 sK3 X1 sK0]
    conv => enter [1]; rw [l32 X0 sK3 sK1]
  have l35 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [h54188 X0 sK1 (sK1 ◇ (X0 ◇ (X0 ◇ X0))) sK1]
    conv => enter [1, 2]; rw [← l33 sK1 X0 X0 X0 sK1]
  have l36 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l35 X0 sK1]
    conv => enter [1]; rw [← l34 X0 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l36 x x y z w]

@[equational_result]
theorem Equation54188_implies_Equation54166 (G : Type*) [Magma G] (h54188 : Equation54188 G) : Equation54166 G := by
  intro x y z
  conv => enter [1]; rw [h54188 x y x z]

theorem Equation4512_54188_implies_Equation53819 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54188 : Equation54188 G) : Equation53819 G := by
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
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK2 ◇ sK1))]
  have l8 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l7 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l9 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h54188 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54188 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l14 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h54188 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l12 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l16 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l9 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l18 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
  have l23 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l24 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l23 sK0 X0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2 X0]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h54188 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0 X0]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2 X0]
  have l27 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l26 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h54188 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l30 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l30 sK0 X0 sK1 sK2]
  have l32 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h54188 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [← l21 sK0 (X1 ◇ X0)]
  have l33 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l31 sK0 sK1 sK2 (X0 ◇ sK0)]
    conv => enter [1]; rw [← h54188 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0 (sK1 ◇ (sK2 ◇ sK1)) sK0]
  have l34 : ∀ X0 X1 sK2 sK1 sK0 : G, (X0 ◇ (X1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK2 sK1 sK0
    conv => enter [1]; rw [← h54188 X0 sK2 X1 sK1]
    conv => enter [1]; rw [l32 X0 sK2 sK0]
  have l35 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54188 X0 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ X0))) sK0]
    conv => enter [1, 2]; rw [← l33 sK0 X0 X0 sK0]
  have l36 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l35 X0 sK0]
    conv => enter [1]; rw [← l34 X0 sK1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l36 x x y z]

theorem Equation4512_53946_implies_Equation53892 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53892 G := by
  have l0 : ∀ sK3 sK0 sK2 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK3 ◇ (((sK0 ◇ sK2) ◇ X0) ◇ X1)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [← h4512 sK3 ((sK0 ◇ sK2) ◇ X0) X1]
  have l1 : ∀ sK3 sK0 sK2 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = (sK3 ◇ ((sK0 ◇ sK2) ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l0 sK3 sK0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK2) X0 X1]
  have l2 : ∀ sK3 sK0 sK2 X0 X1 : G, (((sK3 ◇ (sK0 ◇ sK2)) ◇ X0) ◇ X1) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [l1 sK3 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h53946 (sK0 ◇ sK2) X1 sK3 X0]
  have l3 : ∀ sK3 sK0 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro sK3 sK0 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ (sK0 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l2 sK3 sK0 sK2 X0 X1]
  have l4 : ∀ sK1 sK3 sK0 sK2 X1 X0 : G, ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK1 sK3 sK0 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ (sK0 ◇ sK2)) (X1 ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK3 sK0 sK2 X1 X0]
  have l5 : ∀ sK0 sK2 X0 sK1 sK3 X1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK3 ◇ (sK0 ◇ sK2))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK2 X0 sK1 sK3 X1
    conv => enter [1]; rw [h53946 (sK0 ◇ sK2) X0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK3 sK0 sK2 X1 X0]
  have l6 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK0 sK2]
    conv => enter [1]; rw [← l3 sK3 sK0 sK2 sK1 sK2]
  have l7 : ∀ X0 sK0 sK2 X1 sK3 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = (X1 ◇ (X0 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK2 X1 sK3 sK1
    conv => enter [1]; rw [h53946 X0 (sK0 ◇ sK2) X1 (sK3 ◇ (sK0 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [l6 sK3 sK0 sK2 sK1]
  have l8 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l3 sK3 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [h53946 (sK0 ◇ sK2) sK2 X0 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l3 sK3 sK0 sK2 sK1 sK2]
  have l9 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ (X1 ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK2 (X1 ◇ X0)]
    conv => enter [1]; rw [← h53946 sK2 X0 sK0 X1]
  have l10 : ∀ X0 X1 sK0 sK2 X2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (X2 ◇ X1))) := by
    intro X0 X1 sK0 sK2 X2
    conv => enter [1]; rw [h53946 X0 X1 (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) X2]
    conv => enter [1]; rw [← l5 sK0 sK2 (X2 ◇ X1) X0 X0 X0]
  have l11 : ∀ sK0 sK2 X1 X0 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 sK2 X1 X0
    conv => enter [1]; rw [h53946 (sK0 ◇ sK2) X1 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [← l10 X0 X1 sK0 sK2 sK0]
  have l12 : ∀ X1 sK3 sK0 sK2 sK1 X0 : G, (X1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X1 sK3 sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l8 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l7 X0 sK0 sK2 X1 sK3 sK1]
  have l13 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [← l11 X0 sK2 X1 X0]
    conv => enter [1]; rw [l9 X0 sK2 (X0 ◇ sK2) X1]
  have l14 : ∀ X1 sK3 sK0 sK2 sK1 X0 : G, (X1 ◇ ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro X1 sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l12 X1 sK3 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h53946 X0 sK2 X0 sK0]
  have l15 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l8 sK3 sK0 sK2 sK1 sK3]
    conv => enter [1]; rw [l14 sK3 sK3 sK0 sK2 sK1 X0]
  have l16 : ∀ X0 sK3 sK0 sK2 : G, (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK3 sK0 sK2
    conv => enter [1]; rw [← h53946 sK3 sK2 X0 sK0]
    conv => enter [1]; rw [l13 sK3 sK2 sK2]
  have l17 : ∀ sK3 sK0 sK2 sK1 X0 : G, ((sK3 ◇ (sK0 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1 X0
    conv => enter [1]; rw [l15 sK3 sK0 sK2 sK1 sK2]
    conv => enter [1]; rw [← l16 X0 sK3 sK0 sK2]
  have l18 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l15 sK3 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [l17 sK3 sK0 sK2 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [l18 x y x z w]

theorem Equation4512_53946_implies_Equation53985 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53946 : Equation53946 G) : Equation53985 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ X0) X1]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53946 sK2 X1 sK1 X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK2 X2 sK1 X0 X1 : G, (sK2 ◇ (sK2 ◇ X2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK2 X2 sK1 X0 X1
    conv => enter [1]; rw [← l3 sK1 sK2 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X2 ◇ X1)) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK1 sK2 X2 X1]
  have l6 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l3 sK1 sK2 sK2 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X1 ◇ (X0 ◇ sK2))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 2]; rw [l5 sK1 sK2 sK1 sK2 X0]
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2) (X0 ◇ sK2) X1]
  have l8 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l4 sK2 sK2 sK1 sK2 sK2]
    conv => enter [1]; rw [← l7 sK1 sK2 sK2 sK2]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1]
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2) (sK1 ◇ sK2) sK1]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l6 sK2 sK1]
    conv => enter [1]; rw [l9 sK2 sK1]
  have l11 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l11 sK1 sK2 X0]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l12 sK1 sK2 X0]
  have l14 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l3 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l5 sK1 sK2 sK2 (sK1 ◇ sK2) sK1]
  have l15 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l14 sK2 sK1]
    conv => enter [1]; rw [← l10 sK1 sK2]
  have l16 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l6 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l6 sK2 sK1]
  have l17 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l16 sK1 sK2]
  have l18 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l17 sK1 sK2]
  have l19 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l15 sK2 sK1]
  have l20 : ∀ X0 X1 sK2 X2 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ sK2))) = (X2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK2 X2 sK1
    conv => enter [1]; rw [h53946 X0 (X1 ◇ sK2) X2 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [l5 sK1 sK2 X1 sK2 sK1]
  have l21 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l15 sK2 sK1]
    conv => enter [1]; rw [h53946 sK2 (sK1 ◇ sK2) X0 sK2]
    conv => enter [1, 2]; rw [l15 sK2 sK1]
  have l22 : ∀ sK2 X2 X1 X0 : G, (sK2 ◇ (sK2 ◇ (X2 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 X2 X1 X0
    conv => enter [1]; rw [← l3 sK2 sK2 X0 (X2 ◇ X1)]
    conv => enter [1]; rw [← h53946 X0 X1 (sK2 ◇ sK2) X2]
  have l23 : ∀ sK2 X1 X0 : G, (sK2 ◇ (sK2 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [h53946 sK2 X1 sK2 sK2]
    conv => enter [1]; rw [l22 sK2 sK2 X1 X0]
  have l24 : ∀ X0 X1 sK2 X2 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ sK2))) = (X2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK2 X2 sK1
    conv => enter [1]; rw [l20 X0 X1 sK2 X2 sK1]
    conv => enter [1, 2]; rw [← l21 sK1 sK2 X0]
  have l25 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (X1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [← l24 X0 X1 sK2 sK1 sK1]
  have l26 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l25 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← h53946 X0 sK2 X0 sK1]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l26 sK1 sK2 sK1]
    conv => enter [1]; rw [l18 sK1 sK2]
    conv => enter [1, 2]; rw [l26 sK1 sK2 sK1]
  have l28 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l27 sK1 sK2]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [← l28 sK1 sK2 X0]
  have l30 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l29 sK1 sK2 sK1]
    conv => enter [1]; rw [l3 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l31 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53946 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) X0 sK1]
    conv => enter [1, 2]; rw [← l29 sK1 sK2 sK1]
  have l32 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = ((sK1 ◇ sK2) ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l29 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
  have l33 : ∀ sK2 X1 sK1 : G, (sK2 ◇ (sK2 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro sK2 X1 sK1
    conv => enter [1]; rw [← l3 sK1 sK2 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) X1]
    conv => enter [1]; rw [← l32 sK1 sK2 X1 sK2]
  have l34 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l13 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l31 sK1 sK2 X0]
  have l35 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l30 sK1 sK2]
    conv => enter [1]; rw [← h53946 sK2 (sK1 ◇ sK2) sK2 sK1]
  have l36 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l26 sK1 sK2 sK1]
    conv => enter [1]; rw [l34 sK1 sK2 X0]
  have l37 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [l33 sK2 (sK1 ◇ sK2) sK1]
  have l38 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l26 sK1 sK2 sK1]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0]
  have l39 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 2]; rw [l38 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK1 sK2 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l40 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [l39 sK1 sK2 X0 sK0]
  have l41 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l26 sK1 sK2 sK1]
    conv => enter [1]; rw [l40 sK1 sK2 X0 sK0]
  have l42 : ∀ X0 X1 sK0 sK1 sK2 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X2 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2 X2
    conv => enter [1]; rw [h53946 X0 (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X2 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK2 X1 sK0]
  have l43 : ∀ X0 X1 sK0 sK1 sK2 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = (X2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2 X2
    conv => enter [1]; rw [l42 X0 X1 sK0 sK1 sK2 X2]
    conv => enter [1, 2]; rw [← l36 sK1 sK2 X0]
  have l44 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK1]
    conv => enter [1]; rw [← l43 X0 X1 sK0 sK1 sK2 sK1]
  have l45 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l44 sK1 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [← h53946 X0 (sK0 ◇ (sK1 ◇ sK2)) X0 sK1]
  have l46 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l45 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← h53946 X0 (sK1 ◇ sK2) X0 sK1]
  have l47 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (X0 ◇ ((X0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1, 1]; rw [l46 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ sK2)) X1]
  have l48 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l47 sK1 sK2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ sK2) X1]
  have l49 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l48 sK1 sK2 X1 X0]
    conv => enter [1]; rw [← h53946 X0 X1 X0 (sK1 ◇ sK2)]
  have l50 : ∀ sK2 sK1 X0 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 sK3 sK0
    conv => enter [1]; rw [l23 sK2 (sK1 ◇ sK2) sK3]
    conv => enter [1]; rw [h53946 sK3 (sK1 ◇ sK2) X0 sK0]
  have l51 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [← l33 sK2 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l50 sK2 sK1 X0 sK3 sK0]
  have l52 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [l51 sK1 sK2 X0 sK3 sK0]
  have l53 : ∀ sK1 sK2 X1 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1)) := by
    intro sK1 sK2 X1 X0 sK3 sK0
    conv => enter [1, 1]; rw [l52 sK1 sK2 X0 sK3 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) X1]
  have l54 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l53 sK1 sK2 sK2 (sK1 ◇ sK2) sK1 sK1]
  have l55 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l26 sK1 sK2 sK1]
    conv => enter [1]; rw [l54 sK1 sK2]
  have l56 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← h53946 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [← l49 sK1 sK2 sK2 sK0]
  have l57 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l55 sK1 sK2]
    conv => enter [1]; rw [← l56 X0 sK0 sK1 sK2]
  intro x y z w
  conv => enter [1]; rw [l57 x y z w]

end Semigroup5
