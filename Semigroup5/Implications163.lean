import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41889_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41889 : Equation41889 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41889 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41889 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ X0)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41889 X0 X2 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41889 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l7 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41889 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 X0]
  have l8 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l9 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l8 sK0 X0 X1]
  have l11 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l7 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [l2 (sK0 ◇ sK0) sK0 X0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l11 sK0 X1 X0]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK0) sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l12 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← l10 sK0 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l15 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l14 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l10 sK0 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l15 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l10 sK0 sK0 X0]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41889 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0 sK0]
  have l21 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h41889 X0 (sK0 ◇ sK0) X1]
  have l22 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41889 X0 sK0 X0]
    conv => enter [1]; rw [l21 sK0 X0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l22 X0 sK0]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((X0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l22 X0 sK0]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l24 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l26 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l17 sK0 X0 X1]
    conv => enter [1]; rw [l25 X0 sK0 X1]
  have l27 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [l26 sK0 X0 X1]
  have l28 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l23 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = ((sK0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l27 sK0 X0 X1]
    conv => enter [1]; rw [← l28 sK0 X0 X1]
  have l30 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l31 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l32 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l31 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK0 (sK1 ◇ sK2) (sK0 ◇ sK0)]
  have l33 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l32 sK1 sK0 sK2]
    conv => enter [1]; rw [← l9 sK0 sK0 (sK1 ◇ sK2)]
  have l34 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l33 sK1 sK0 sK2]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [l2 sK1 sK0 sK2]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1 sK0]
    conv => enter [1]; rw [← l30 sK0 sK1 sK0]
  have l37 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41889 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l36 sK0 sK1]
  have l38 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
  have l39 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ sK1) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l38 sK0 X0 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1 X0]
  have l40 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l37 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1 sK1]
  have l41 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l39 sK0 X0 sK0]
  have l42 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l27 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l40 sK1 X0 sK0]
  have l43 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l41 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l44 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l42 sK1 sK2 sK0]
    conv => enter [1]; rw [← l43 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l44 y z x]

@[equational_result]
theorem Equation41_implies_Equation41891 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41891 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41891_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41891 : Equation41891 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41891 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h41891 (X0 ◇ X0) X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41891 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X2))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41891 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X2 ◇ X2))) X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41891 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ X3)))]
  have l5 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h41891 X0 sK0 X1]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← h41891 X0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41891 X0 X2 X0]
  have l8 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X2 ◇ X2)) X3]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l11 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l8 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X2) X3]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h41891 X0 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2, 2]; rw [l6 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l11 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X2 X3]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41891 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK0 X0]
  have l17 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l14 X0 X1 X3 X2]
  have l18 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l17 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← l15 X0 (X2 ◇ (X2 ◇ X3))]
  have l19 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l18 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← l15 X2 X3]
  have l20 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41891 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l16 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 sK0 X0]
    conv => enter [1]; rw [← h41891 X0 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ X0)]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41891 X0 X2 X1]
    conv => enter [1, 2]; rw [← l15 X0 (X1 ◇ X1)]
  have l24 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X2 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l23 X0 X2 X1]
    conv => enter [1]; rw [← l19 X0 X2 X1 X1]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) sK0 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [← l24 sK0 (sK0 ◇ sK0) X0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l21 sK0 sK0]
    conv => enter [1]; rw [← l26 sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← h41891 X0 sK0 sK0]
  have l29 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l28 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l30 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0]
    conv => enter [1]; rw [← l29 sK0 X0 X1]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [l30 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

@[equational_result]
theorem Equation41_implies_Equation41892 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41892 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y x]

theorem Equation4512_41892_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41892 : Equation41892 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41892 X1 X2 X0 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41892 X0 X1 X1 X1]
  have l2 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41892 (sK0 ◇ sK0) X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41892 X0 X1 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41892 X0 X0 X0 X0]
  have l4 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ X2) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h41892 sK0 X2 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h41892 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X2 ◇ X3))) X4]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41892 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ X4)))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2 X0 X0]
    conv => enter [1, 2]; rw [← h41892 X0 X2 X0 X0]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X2 ◇ X3)) X4]
  have l9 : ∀ sK0 X1 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l4 sK0 X1 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 X1 sK0]
  have l10 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l11 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X4) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41892 X0 X1 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l10 X0 X1 X4 X0 X0]
  have l12 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h41892 X0 (sK0 ◇ sK0) X1 X2]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0 X0 X0]
    conv => enter [1]; rw [← h41892 X0 sK0 X0 X0]
  have l14 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← l3 X0 (X0 ◇ X0)]
  have l15 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l3 X0 sK0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X0)]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 X0 X0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l18 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1, 2]; rw [← l1 X1 X0 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← l14 X0 X1]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ sK0)]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l18 X0 X1 X2]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l22 X0 X1]
    conv => enter [1]; rw [← l21 X1 X0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l21 sK0 X0 sK0]
  have l25 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK0 sK2]
  have l26 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
  have l27 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l21 sK2 sK1 sK0]
    conv => enter [1]; rw [← l26 sK1 sK2 sK0]
  have l28 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l27 sK2 sK1 sK0]
    conv => enter [1]; rw [l13 (sK1 ◇ sK2) sK0]
  have l29 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l28 sK2 sK1 sK0]
    conv => enter [1]; rw [l23 (sK1 ◇ sK2) sK0]
  have l30 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l24 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l29 sK2 sK1 sK0]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l23 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [← l31 y z x]

@[equational_result]
theorem Equation41_implies_Equation41895 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41895 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41895_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41895 : Equation41895 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41895 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h41895 X1 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41895 X0 X1 X1]
  have l3 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h41895 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ X0))]
  have l4 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (((sK0 ◇ sK0) ◇ X0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← l2 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l6 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (sK2 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l2 X0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK2 sK1 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 sK0]
  have l8 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ sK2)) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2 X1
    conv => enter [1]; rw [l6 X0 sK1 sK2]
    conv => enter [1]; rw [← l6 X1 sK1 sK2]
  have l9 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ sK1) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [← l6 (X0 ◇ X1) sK1 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK2)]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← l2 X0 (sK0 ◇ sK0)]
  have l15 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l8 X0 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l14 sK0 (sK1 ◇ sK2)]
  have l16 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l6 sK2 sK1 sK2]
    conv => enter [1]; rw [l15 sK2 sK1 sK2 sK0]
  have l17 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1, 2]; rw [← l6 X0 sK1 sK2]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l2 (X0 ◇ sK0) (sK0 ◇ sK0)]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2 sK1]
    conv => enter [1]; rw [← l9 sK2 sK1 sK2 sK1]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [l16 sK2 sK1 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l24 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK0]
    conv => enter [1]; rw [← l23 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l24 y z x]

@[equational_result]
theorem Equation41_implies_Equation41898 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41898 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_41898_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41898 : Equation41898 G) : Equation41 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h41898 X0 X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41898 X0 X0 X0]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41898 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l5 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X3) := by
    intro X0 X1 X3
    conv => enter [1]; rw [h41898 X0 X1 (X0 ◇ X3)]
    conv => enter [1]; rw [← l4 X0 X1 X3 X0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [l5 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← l7 sK0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK1)))]
    conv => enter [1]; rw [← h41898 X0 (sK1 ◇ sK2) sK1]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l8 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation41899 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41899 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK0]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41899_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41899 : Equation41899 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ ((sK0 ◇ X0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41899 (sK0 ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41899 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h41899 (X1 ◇ X0) X0 (X1 ◇ X0)]
    conv => enter [1, 2]; rw [← h41899 X0 (X1 ◇ X0) X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41899 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41899 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ sK1)]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41899 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41899 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0)))]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41899 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (X1 ◇ X0)))]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X3 ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l10 sK0 X0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l13 sK0 X0 X1]
    conv => enter [1]; rw [← l9 X0 X1 sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [l11 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l15 sK0 X0 X1]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l16 sK0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ sK0) sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l17 sK0 sK0 (sK0 ◇ sK0)]
  have l23 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l20 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l23 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l12 X0 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [l26 sK0 X0]
  have l28 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41899 (X0 ◇ (sK0 ◇ sK0)) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l27 sK0 X0]
  have l29 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l28 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X1 X0 sK0
    conv => enter [1, 2, 2]; rw [l27 sK0 X1]
    conv => enter [1]; rw [← l29 X0 sK0 X1]
  have l31 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [← l30 X1 X0 sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1, 2]; rw [← l23 sK0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41899 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l16 sK0 X0]
  have l34 : ∀ X0 sK0 X1 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l16 sK0 X0]
  have l35 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l16 sK0 sK2]
  have l36 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [← l31 sK0 sK0 sK1]
  have l37 : ∀ X0 sK0 X1 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l34 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1, 2]; rw [← l31 sK0 sK0 (sK0 ◇ sK0)]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l32 sK0 X0]
  have l40 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK0]
    conv => enter [1]; rw [← l24 sK0 sK1]
  have l41 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l24 sK0 X1]
    conv => enter [1]; rw [← l37 X0 sK0 X1]
  have l42 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0]
    conv => enter [1, 2]; rw [← l16 sK0 sK0]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l40 sK1 sK0 sK0]
  have l44 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l41 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0 X0]
    conv => enter [1, 2]; rw [← l39 sK0 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK0]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l47 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l44 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l25 sK0 X1]
  have l48 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l39 sK0 X0]
    conv => enter [1]; rw [← l45 sK0 X0]
  have l49 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l46 sK0 sK1]
  have l50 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [← l31 (sK1 ◇ sK2) sK0 sK2]
  have l51 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
    conv => enter [1]; rw [← l47 sK0 sK2 (sK1 ◇ sK2)]
  have l52 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l51 sK1 sK2 sK0]
    conv => enter [1]; rw [← l48 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l52 y z x]

@[equational_result]
theorem Equation41_implies_Equation41901 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41901 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK2) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK2)))]
  intro x y z
  conv => enter [1]; rw [← h41 z x y]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41901_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41901 : Equation41901 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = (X0 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [h41901 (X1 ◇ X1) X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41901 X0 (X1 ◇ X1) X1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41901 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ X0)]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h41901 sK1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ X0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41901 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X0)]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X0))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ (((sK1 ◇ sK2) ◇ (X0 ◇ X0)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 ((sK1 ◇ sK2) ◇ (X0 ◇ X0))]
    conv => enter [1, 2]; rw [← h41901 ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) (sK1 ◇ sK2) X0]
  have l10 : ∀ sK2 sK1 X0 X1 : G, (sK2 ◇ (((sK1 ◇ sK2) ◇ (X0 ◇ X0)) ◇ X1)) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK2 ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l3 sK1 sK2 X0]
  have l11 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l10 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) (X0 ◇ X0) X1]
  have l12 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ ((X0 ◇ X0) ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l9 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK2) (X0 ◇ X0) (sK1 ◇ sK2)]
  have l13 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l11 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l14 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (sK1 ◇ sK2)]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l14 sK1 sK2 sK1]
    conv => enter [1]; rw [← l13 sK1 sK2 (sK1 ◇ sK2) sK1]
  have l16 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK2]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l16 sK1 sK2]
    conv => enter [1, 2]; rw [← l15 sK1 sK2]
  have l18 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l19 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l18 sK1 sK2]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l20 sK1 sK2 sK0]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ sK2) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l22 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l15 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l26 y z x]

@[equational_result]
theorem Equation41_implies_Equation41902 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41902 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 sK0]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y x]

theorem Equation4512_41902_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41902 : Equation41902 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h41902 X1 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41902 X0 X1 X1 X1]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41902 (sK0 ◇ sK0) sK0 X0 X1]
    conv => enter [1, 2]; rw [l0 sK0 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41902 X0 X1 X2 X3]
  have l4 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [l3 X1 X0 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1))]
  have l6 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [← l4 X1 X0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l7 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((X0 ◇ X1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [← l1 (X0 ◇ X1) (sK0 ◇ sK0)]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l6 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X3) X4]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l7 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l10 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X4)) := by
    intro X0 X1 X4
    conv => enter [1]; rw [h41902 X0 X1 (X0 ◇ X0) X4]
    conv => enter [1]; rw [← l8 X0 X1 X4 X0 X0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0 X1]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l10 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0 X0 X1]
  have l13 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l12 X0 X1 X0]
    conv => enter [1]; rw [← l12 sK1 sK2 X0]
  intro x y z
  conv => enter [1]; rw [l13 x x y z]

@[equational_result]
theorem Equation41_implies_Equation41903 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41903 G := by
  have l0 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h41 sK0 sK1 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41903_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41903 : Equation41903 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41903 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41903 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41903 X0 sK0 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 X0 sK0]
    conv => enter [1]; rw [← h41903 X0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [l4 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41903 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l2 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41903 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2]; rw [← l8 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h41903 X0 (sK0 ◇ sK0) X1]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41903 X0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 X0]
  have l14 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l13 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l15 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l14 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = (sK0 ◇ X1) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [← l15 sK0 X1 X0]
    conv => enter [1]; rw [← l8 sK0 X1]
  have l17 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l19 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l8 sK0 X1]
    conv => enter [1]; rw [l18 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X1]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [← l16 X0 sK0 X1]
    conv => enter [1]; rw [← l19 sK0 X1 X0]
  have l21 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (sK0 ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [← l16 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 X1]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41903 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l21 sK0 (X0 ◇ X0)]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41903 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 (X0 ◇ (sK0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h41903 X0 sK0 sK0]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l12 X0 sK0]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l26 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l24 sK0 X0]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1]; rw [← l25 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l28 y z x]

@[equational_result]
theorem Equation41_implies_Equation41905 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41905 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41905_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41905 : Equation41905 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ X1) = (X1 ◇ (sK1 ◇ ((sK2 ◇ X0) ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [h41905 sK1 X1 (sK2 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41905 X0 X2 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41905 X0 (X1 ◇ (X0 ◇ X1)) X1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41905 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41905 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ X3)))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41905 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41905 X0 X2 X0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l8 : ∀ X0 X2 : G, (X0 ◇ X2) = (X2 ◇ (X0 ◇ X0)) := by
    intro X0 X2
    conv => enter [1]; rw [l2 X0 X2 X0]
    conv => enter [1, 2]; rw [← h41905 X0 X0 X0]
  have l9 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ X1) = (X1 ◇ (sK1 ◇ (sK2 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l1 sK1 X1 sK2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 X0 ((sK1 ◇ sK2) ◇ X0)]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41905 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l7 sK0 X0]
  have l11 : ∀ sK1 X1 sK2 X0 : G, (sK1 ◇ X1) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro sK1 X1 sK2 X0
    conv => enter [1]; rw [l9 sK1 X1 sK2 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ ((sK1 ◇ sK2) ◇ X0))]
  have l12 : ∀ sK1 X1 sK2 : G, (sK1 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l11 sK1 X1 sK2 sK1]
    conv => enter [1]; rw [← h41905 (sK1 ◇ sK2) X1 sK1]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [l12 sK1 (sK2 ◇ X0) sK2]
  have l14 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ sK1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← l12 sK1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) sK2]
    conv => enter [1]; rw [← h41905 X0 sK1 X1]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (sK1 ◇ sK2)) = (X0 ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h41905 X0 (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [l14 sK1 sK2 X0 X0]
  have l16 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41905 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0 X0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h41905 X0 (sK0 ◇ sK0) X1]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41905 X0 sK0 X0]
    conv => enter [1]; rw [l17 sK0 X0 X0]
  have l19 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l16 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l18 X0 sK0]
  have l22 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK2 sK1
    conv => enter [1]; rw [l8 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 sK2]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2 sK2]
    conv => enter [1]; rw [← l23 sK2 sK1]
  have l25 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l22 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l24 sK1 sK2]
    conv => enter [1]; rw [← l15 sK2 sK1 sK2]
  have l27 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l25 X0 X1 X2]
  have l28 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h41905 sK2 X0 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l26 sK1 sK2]
  have l29 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l28 sK2 X0 sK1]
    conv => enter [1, 2]; rw [l6 sK2 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l30 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l29 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l13 sK1 sK2 (sK1 ◇ sK2)]
  have l31 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l30 sK2 X0 sK1]
    conv => enter [1]; rw [← l8 (sK1 ◇ sK2) X0]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [l31 sK2 (sK1 ◇ sK2) sK1]
  have l33 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l8 sK2 X0]
    conv => enter [1, 2]; rw [l31 sK2 sK2 sK1]
  have l34 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = ((sK1 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l8 X0 sK2]
    conv => enter [1]; rw [l31 sK2 (X0 ◇ X0) sK1]
  have l35 : ∀ X0 sK2 sK1 : G, (X0 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l34 X0 sK2 sK1]
    conv => enter [1]; rw [← l8 X0 (sK1 ◇ sK2)]
  have l36 : ∀ sK2 X0 sK1 : G, (sK2 ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l33 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 sK2]
  have l37 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ X0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l8 (sK1 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← l32 sK1 sK2]
  have l38 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ X1) = (X1 ◇ (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [h41905 sK2 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l36 sK2 X0 sK1]
  have l39 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ X1) = (X1 ◇ (X0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [l38 sK2 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l27 X0 sK2 (sK1 ◇ sK2)]
  have l40 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [l39 sK2 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l37 sK1 sK2 sK2]
  have l41 : ∀ sK2 X1 X0 sK1 : G, (sK2 ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)))) := by
    intro sK2 X1 X0 sK1
    conv => enter [1]; rw [l40 sK2 X1 X0 sK1]
    conv => enter [1, 2, 2]; rw [l35 (sK1 ◇ sK2) sK2 sK1]
  have l42 : ∀ sK2 X1 sK1 X0 : G, (sK2 ◇ X1) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 X1 sK1 X0
    conv => enter [1]; rw [l41 sK2 X1 X0 sK1]
    conv => enter [1, 2]; rw [← l8 (sK1 ◇ sK2) X0]
  have l43 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ X1) = (X1 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l31 sK2 X1 sK1]
    conv => enter [1]; rw [l42 sK2 X1 sK1 X0]
  have l44 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h41905 X0 X1 (sK1 ◇ sK2)]
    conv => enter [1, 2, 2, 2]; rw [← l37 sK1 sK2 X0]
  have l45 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ X0))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l44 X0 X1 sK1 sK2]
    conv => enter [1, 2]; rw [← l27 (sK1 ◇ sK2) X0 X0]
  have l46 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l45 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l43 sK1 sK2 X1 (X0 ◇ X0)]
  have l47 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l46 X0 sK0 sK1 sK2]
  have l48 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [← l46 X0 (sK1 ◇ sK2) sK1 sK2]
  have l49 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 X0 sK1 sK2]
    conv => enter [1]; rw [l21 (sK1 ◇ sK2) sK0]
  have l50 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ sK2) = (sK0 ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l48 sK1 sK2 sK0]
    conv => enter [1]; rw [← l49 sK0 X0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l50 x x y z]

@[equational_result]
theorem Equation41_implies_Equation41906 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41906 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK3 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41906_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41906 : Equation41906 G) : Equation41 G := by
  have l0 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41906 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41906 X1 X2 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41906 X0 X1 X1 X1]
  have l2 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X0 ◇ X2)))]
    conv => enter [1, 2]; rw [← h41906 X0 sK0 X1 X2]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h41906 X0 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [l0 X2 X4 X0 X1 X3]
    conv => enter [1]; rw [← l1 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4 X2]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [l4 X2 X4 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l7 : ∀ X2 X4 X0 : G, (X2 ◇ X4) = (X4 ◇ X0) := by
    intro X2 X4 X0
    conv => enter [1]; rw [l6 X2 X4 X0 X2 X2]
    conv => enter [1]; rw [← l1 X4 X0 (X2 ◇ (X2 ◇ X2))]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 sK0]
    conv => enter [1]; rw [← l1 (sK0 ◇ sK0) X0 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l10 y z x]

@[equational_result]
theorem Equation41_implies_Equation41907 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41907 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41907_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41907 : Equation41907 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41907 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41907 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l4 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41907 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 X0]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l1 sK0 X0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l5 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (X1 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l3 sK0 sK0]
  have l9 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l7 X0 sK0 X1]
    conv => enter [1]; rw [← l6 sK0 (X1 ◇ (sK0 ◇ sK0)) X0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [← l9 X0 sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1, 2]; rw [← l12 sK0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l15 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
  have l16 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l11 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l3 sK0 X1]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l15 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l19 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X1
    conv => enter [1]; rw [l17 sK0 sK0 ((sK0 ◇ sK0) ◇ X1)]
    conv => enter [1]; rw [← l18 sK0 X1 sK0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41907 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l19 sK0 (X1 ◇ X0)]
  have l21 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l21 X0 X1 sK0]
    conv => enter [1]; rw [← l14 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l22 y z x]

@[equational_result]
theorem Equation41_implies_Equation41909 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41909 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41909_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41909 : Equation41909 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h41909 X0 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41909 (X0 ◇ X1) X0 X1]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41909 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← h41909 sK0 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l7 sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41909 X0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l8 sK0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41909 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l9 sK0 (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))]
    conv => enter [1, 2]; rw [← h41909 X0 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41909 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l9 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) X0]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← l13 X0 sK0]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (sK0 ◇ X0))]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1]; rw [← l3 X0 sK0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41909 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0 X1]
  have l20 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l21 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l15 sK0 X1]
    conv => enter [1]; rw [l20 sK0 X1 X0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l21 sK0 sK0 X0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK0]
    conv => enter [1]; rw [← l21 sK0 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l24 y z x]

@[equational_result]
theorem Equation41_implies_Equation41910 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41910 G := by
  have l0 : ∀ sK3 sK2 sK0 sK1 : G, (sK3 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK3 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z y w x]

theorem Equation4512_41910_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41910 : Equation41910 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [h41910 X4 X2 (X0 ◇ X1) X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l2 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41910 X1 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41910 X1 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41910 X0 X1 X2 X1]
  have l4 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ sK0) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l2 X1 sK0 X0]
    conv => enter [1]; rw [← l3 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) sK0 X1]
  have l5 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X2) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [l1 X4 X2 X0 X1 X3]
    conv => enter [1]; rw [← l3 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X2 X4]
  have l6 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l4 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ X0) sK0]
  have l7 : ∀ X4 X2 X0 X1 X3 : G, (X4 ◇ X2) = (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X2)) := by
    intro X4 X2 X0 X1 X3
    conv => enter [1]; rw [l5 X4 X2 X0 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X2]
  have l8 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ sK0) := by
    intro sK0 X1
    conv => enter [1]; rw [l3 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1]; rw [← l6 X1 sK0 sK0]
  have l9 : ∀ X2 X0 X4 : G, (X2 ◇ X0) = (X4 ◇ X2) := by
    intro X2 X0 X4
    conv => enter [1]; rw [l3 X2 X0 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← l7 X4 X2 X0 X2 X2]
  have l10 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l8 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l9 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation41_implies_Equation41911 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41911 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h41 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41911_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41911 : Equation41911 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41911 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41911 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41911 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ X0)))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41911 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X0 ◇ sK0))]
  have l5 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41911 X0 sK0 X1]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 X0 sK0]
    conv => enter [1]; rw [← h41911 X0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41911 X0 X2 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) X0 sK0]
  have l11 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h41911 X0 (sK0 ◇ sK0) X1]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41911 X0 sK0 X0]
    conv => enter [1]; rw [l11 sK0 X0 X0]
  have l13 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41911 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l12 X0 sK0]
  have l14 : ∀ sK0 X1 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [l13 sK0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41911 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [l14 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l12 X0 sK0]
  have l18 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41911 (sK0 ◇ sK0) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 X0]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l18 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l2 X0 (sK0 ◇ sK0) sK0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l10 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l19 sK0 X1 X0]
    conv => enter [1, 2]; rw [← l12 X0 sK0]
  have l22 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l12 X0 sK0]
  have l23 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l10 sK0 X1]
    conv => enter [1]; rw [l21 sK0 X1 X0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l22 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [l6 sK0 X0]
  have l25 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [← l12 X0 sK0]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l25 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l23 sK0 X0 X0]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1, 2]; rw [l15 sK0 X0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← l12 X0 sK0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l15 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1, 2]; rw [← l10 sK0 X1]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1, 2]; rw [← l12 X0 sK0]
  have l32 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = ((sK0 ◇ X0) ◇ X1) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l26 X1 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 X0 X1]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 sK0 X0]
    conv => enter [1]; rw [← l31 sK0 X0]
  have l34 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ (X0 ◇ X1)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l32 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 X1]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l36 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 sK2]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l36 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 (sK0 ◇ sK0) sK2]
  have l38 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ sK0) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l37 sK1 sK2 sK0]
    conv => enter [1]; rw [← l10 sK0 (sK1 ◇ sK2)]
  have l39 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l34 sK2 sK1 sK0]
    conv => enter [1]; rw [← l38 sK1 sK2 sK0]
  have l40 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l39 sK2 sK1 sK0]
    conv => enter [1]; rw [l28 (sK1 ◇ sK2) sK0]
  have l41 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l35 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l40 sK2 sK1 sK0]
  have l42 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [h41911 sK1 X0 sK2]
    conv => enter [1, 2, 2, 2]; rw [← l41 sK0 sK2 sK1]
  have l43 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0))) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l42 sK1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (sK0 ◇ sK0)]
  have l44 : ∀ sK1 X0 sK2 sK0 : G, (sK1 ◇ X0) = (X0 ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK1 X0 sK2 sK0
    conv => enter [1]; rw [l43 sK1 X0 sK2 sK0]
    conv => enter [1, 2]; rw [← l12 (sK1 ◇ sK2) sK0]
  have l45 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l23 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l44 sK1 X0 sK0 sK0]
  have l46 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK1 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [l45 sK0 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l46 x y z]

@[equational_result]
theorem Equation41_implies_Equation41914 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41914 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK3 ◇ sK0)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK3 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK3 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z w y x]

theorem Equation4512_41914_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41914 : Equation41914 G) : Equation41 G := by
  have l0 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41914 X1 X2 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41914 X1 X2 X0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41914 X0 X1 X0 X1]
  have l2 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X1 ◇ X2)))]
    conv => enter [1, 2]; rw [← h41914 X0 sK0 X1 X2]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h41914 X0 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (((sK0 ◇ sK0) ◇ X0) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l0 X1 X2 sK0 X0]
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK0) ◇ X0) X2 X1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l4 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X2]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l6 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l1 X2 (sK0 ◇ sK0) X1]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l7 X1 X2 sK0]
    conv => enter [1]; rw [← l5 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation41915 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41915 G := by
  have l0 : ∀ sK3 sK0 sK1 sK2 : G, (sK3 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK1)]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w x y]

theorem Equation4512_41915_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41915 : Equation41915 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41915 (X1 ◇ X0) X2 X0 X1]
    conv => enter [1, 2]; rw [← h41915 X0 (X1 ◇ X0) X1 X1]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41915 sK0 X1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X0))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h41915 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ (X3 ◇ X0))) X4]
  have l4 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro sK0 X0 X1 X2
    conv => enter [1, 2]; rw [h41915 X0 sK0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h41915 X0 (sK0 ◇ sK0) sK0 sK0]
  have l6 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ X0)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ (X3 ◇ X0)) X4]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ X0) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l6 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ X0) X4]
  have l9 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 X0 X4]
  have l10 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X4]
    conv => enter [1]; rw [l9 X0 X1 X4 X2 X3]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l5 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ sK0)]
  have l12 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ sK0) ◇ X1) = (X1 ◇ ((X0 ◇ sK0) ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h41915 (X0 ◇ sK0) X1 X2 sK0]
    conv => enter [1, 2, 2, 2]; rw [l5 sK0 X0]
  have l13 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ sK0) ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l12 X0 sK0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (X2 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 sK0 X0]
    conv => enter [1]; rw [← l11 sK0 X0]
  have l15 : ∀ X0 sK0 X1 : G, ((X0 ◇ sK0) ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l13 X0 sK0 X1 X0]
    conv => enter [1]; rw [← l10 X0 X1 (sK0 ◇ sK0) sK0 X0]
  have l16 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [← l15 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41915 (sK0 ◇ sK0) X0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l14 sK0 sK0]
  have l19 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X2 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h41915 (X0 ◇ (sK0 ◇ sK0)) X1 X2 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 X0]
  have l20 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l19 X0 sK0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (X2 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [l16 X0 (sK0 ◇ sK0) sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l16 sK0 (sK0 ◇ sK0) sK0]
  have l23 : ∀ X0 sK0 X1 X2 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [l20 X0 sK0 X1 X2]
    conv => enter [1, 2]; rw [l7 X0 (sK0 ◇ sK0) X2]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [l16 X0 sK0 sK0]
  have l25 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [l16 sK0 sK0 sK0]
  have l26 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X1 ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ sK0) X1]
    conv => enter [1]; rw [l23 X0 sK0 X1 X2]
  have l27 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l27 sK0]
    conv => enter [1]; rw [l24 sK0 sK0]
  have l29 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41915 (sK0 ◇ sK0) X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l28 sK0]
  have l30 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l29 sK0 X0 X1]
    conv => enter [1]; rw [l7 X0 (sK0 ◇ sK0) X1]
  have l31 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1, 2]; rw [← l24 sK0 X0]
  have l32 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [h41915 (sK0 ◇ sK0) X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0 X0]
  have l33 : ∀ sK0 X1 X2 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X2 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X2 X0
    conv => enter [1]; rw [l32 sK0 X1 X2 X0]
    conv => enter [1]; rw [← l30 sK0 (X2 ◇ ((sK0 ◇ sK0) ◇ X0)) X1]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1]; rw [← l30 sK0 X0 (sK0 ◇ sK0)]
  have l35 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l33 sK0 X1 sK0 X0]
    conv => enter [1]; rw [← l26 X0 sK0 (sK0 ◇ sK0) sK0]
  have l36 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l35 sK0 X1 X0]
    conv => enter [1]; rw [l16 X0 (sK0 ◇ sK0) sK0]
  have l37 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l36 sK0 X1 X0]
    conv => enter [1]; rw [l16 X0 sK0 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 sK0]
    conv => enter [1]; rw [l37 sK0 sK0 X0]
  have l39 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41915 X0 X1 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l34 sK0 (X0 ◇ X0)]
  have l40 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l39 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l38 sK0 X0]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l40 X0 X1 sK0]
    conv => enter [1]; rw [← l38 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l41 y z x]

@[equational_result]
theorem Equation41_implies_Equation41917 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41917 G := by
  have l0 : ∀ sK3 sK0 sK2 sK1 : G, (sK3 ◇ (sK0 ◇ sK3)) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK3)]
    conv => enter [1]; rw [h41 sK3 sK2 (sK1 ◇ (sK3 ◇ (sK0 ◇ sK3)))]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 (sK0 ◇ sK3)]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]
  conv => enter [1]; rw [l0 z w y x]

theorem Equation4512_41917_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41917 : Equation41917 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41917 X0 X1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ X4) = (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1))))) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [h41917 X3 X4 (X1 ◇ (X2 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [← h41917 X0 (X1 ◇ (X2 ◇ X1)) X1 X2]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41917 X2 X3 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h41917 (X0 ◇ X1) X2 X1 X0]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l3 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X3 X4 X0 : G, (X3 ◇ X4) = (X4 ◇ (X0 ◇ X3)) := by
    intro X3 X4 X0
    conv => enter [1]; rw [l2 X3 X4 X0 X3 X3]
    conv => enter [1, 2]; rw [← h41917 X0 X3 X3 X3]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 (sK0 ◇ sK0) X1 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l0 sK0 X1]
    conv => enter [1]; rw [← l7 X0 (sK0 ◇ X1) sK0]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l5 X1 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X1 X0]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (X1 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l9 X1 X0 sK0]
    conv => enter [1]; rw [← l5 X1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK1]
    conv => enter [1]; rw [← l7 X0 sK2 sK1]
  have l12 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ sK2) = (X0 ◇ sK0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l11 sK1 sK2 X0]
    conv => enter [1]; rw [l10 X0 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l12 x x y z]

@[equational_result]
theorem Equation41_implies_Equation41918 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41918 G := by
  have l0 : ∀ sK3 sK0 sK1 : G, (sK3 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [← h41 sK3 sK3 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h41 sK3 sK1 (sK3 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK2 sK1 sK3 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2 sK1 sK3
    conv => enter [1]; rw [h41 sK0 sK2 (sK3 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l0 sK3 sK0 sK1]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ (sK3 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK2 sK1 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

theorem Equation4512_41918_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41918 : Equation41918 G) : Equation41 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41918 X0 X1 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41918 X1 X2 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41918 X0 X1 (X1 ◇ X1) X1]
  have l2 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1, 2]; rw [← h41918 X0 sK0 X1 X2]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0 sK0 sK0]
    conv => enter [1]; rw [← h41918 X0 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (((sK0 ◇ sK0) ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0]
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK0) ◇ sK0) X1 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l4 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l1 X1 (sK0 ◇ sK0) sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← l5 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation41919 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41919 G := by
  have l0 : ∀ sK4 sK1 sK0 sK3 sK2 : G, (sK4 ◇ (sK1 ◇ sK0)) = (sK3 ◇ (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK1 sK0 sK3 sK2
    conv => enter [1]; rw [← h41 sK4 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h41 sK4 sK3 (sK2 ◇ (sK4 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK4 (sK1 ◇ sK0)]
  intro x y z w u
  conv => enter [1]; rw [l1 x y z w u]
  conv => enter [1]; rw [l0 z w u y x]

theorem Equation4512_41919_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41919 : Equation41919 G) : Equation41 G := by
  have l0 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (X2 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41919 X1 X2 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41919 X1 X2 X0 X1 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h41919 X0 X1 X1 X1 X1]
  have l2 : ∀ sK0 X0 X1 X2 X3 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [← h4512 sK0 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
    conv => enter [1, 2]; rw [← h41919 X0 sK0 X1 X2 X3]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 sK0 X0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41919 X0 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l4 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (((sK0 ◇ sK0) ◇ X0) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l0 X1 X2 sK0 X0]
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK0) ◇ X0) X2 X1]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
    conv => enter [1]; rw [l3 sK0 X0]
  have l6 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = ((sK0 ◇ sK0) ◇ (X0 ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l4 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X2]
  have l7 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (X2 ◇ (sK0 ◇ sK0)) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l6 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l1 X2 (sK0 ◇ sK0) X1]
  have l8 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (sK0 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l7 X1 X2 sK0]
    conv => enter [1]; rw [← l5 sK0 X2]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation41957 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41957 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (z ◇ (x ◇ (x ◇ x)))]

theorem Equation4512_41957_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41957 : Equation41957 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41957 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41957 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h41957 X0 (sK0 ◇ sK0) sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41957 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK0]
  have l6 : ∀ X2 X3 X0 : G, (X2 ◇ X3) = (X3 ◇ (X2 ◇ X0)) := by
    intro X2 X3 X0
    conv => enter [1]; rw [l1 X2 X3 X0 X2]
    conv => enter [1, 2]; rw [← h41957 X2 X0 X2]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ sK0)]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41957 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l4 (sK1 ◇ sK2) sK0]
    conv => enter [1]; rw [← h4512 sK1 sK2 sK0]
  have l11 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK2 ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK2 sK1 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X1 ◇ X0) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l13 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l4 (sK1 ◇ sK2) sK0]
  have l14 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK2 ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l12 sK0 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l13 sK2 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l17 sK0 sK1]
  have l19 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
  have l20 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l19 sK0 X0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0 X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0 sK0]
    conv => enter [1]; rw [← l12 sK0 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [← l22 sK0 X0]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41957 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l23 sK0 (X0 ◇ (X0 ◇ X0))]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h41957 X0 (sK0 ◇ sK0) sK0]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l24 X0 X1 sK0]
    conv => enter [1]; rw [← l25 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l26 y z x]

@[equational_result]
theorem Equation41_implies_Equation41959 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41959 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41959_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41959 : Equation41959 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41959 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h41959 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41959 X0 (X0 ◇ X0) X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41959 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ X3)))]
  have l4 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1, 2]; rw [← h41959 X0 sK0 X1]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41959 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l4 sK0 X0 X0]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h41959 X0 X2 X0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41959 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41959 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l10 sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l9 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X1]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1, 2]; rw [l6 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) sK0 sK0]
  have l15 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ X1)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [l12 sK0 X0 X1]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l7 sK0 sK0]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41959 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l16 sK0 X0]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41959 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l20 X0 X1 sK0]
    conv => enter [1]; rw [l20 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l20 X0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 sK0]
    conv => enter [1]; rw [← l24 X0 sK0]
  have l26 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l26 X0 X1 sK0]
    conv => enter [1]; rw [← l22 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l27 X0 X1 sK0]
    conv => enter [1]; rw [← l25 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [← l28 y z x]

@[equational_result]
theorem Equation41_implies_Equation41960 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41960 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41960_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41960 : Equation41960 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41960 X1 X2 X3 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41960 X0 X1 X1 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h41960 X0 X2 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41960 X0 X1 X0 X0]
  have l2 : ∀ X1 X2 X3 : G, (X1 ◇ X2) = (X3 ◇ X2) := by
    intro X1 X2 X3
    conv => enter [1]; rw [l0 X1 X2 X3 X1]
    conv => enter [1]; rw [← l1 X3 X2 (X1 ◇ X1)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l1 X1 X0 sK0]
    conv => enter [1]; rw [← l3 sK0 X0 X1]
  intro x y z
  conv => enter [1]; rw [← l4 y z x]

@[equational_result]
theorem Equation41_implies_Equation41961 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41961 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41961_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41961 : Equation41961 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41961 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41961 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ (X1 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41961 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h41961 sK0 sK0 X0]
  have l4 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l3 X0 sK0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l6 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l4 X0 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l6 X0 sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0]
  have l8 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l7 X0 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l9 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l8 sK0 X1 X0]
  have l10 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 X0 sK0 X1]
  have l11 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l10 X0 sK0 X1]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l11 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [← l13 sK0]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [h41961 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK0]
  have l17 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l16 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41961 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2]; rw [← l16 sK0 X0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l18 sK0 X0 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41961 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l19 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ X0))]
    conv => enter [1]; rw [← h41961 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← l20 sK0 X0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41961 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK0 (X0 ◇ (X1 ◇ X0))]
  have l24 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK0]
    conv => enter [1]; rw [← l21 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l24 y z x]

@[equational_result]
theorem Equation41_implies_Equation41963 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41963 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41963_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41963 : Equation41963 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41963 X1 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2, 2]; rw [← h41963 X0 X1 X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41963 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41963 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l0 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X2) (X0 ◇ X1)]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2 X0]
    conv => enter [1]; rw [← l3 X0 X1 X2 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X1)]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l6 X1 X2 X0]
    conv => enter [1]; rw [← l5 X2 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1)))]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l7 sK0 sK1 sK2]
    conv => enter [1]; rw [← l7 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l8 y z x]

@[equational_result]
theorem Equation41_implies_Equation41964 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41964 G := by
  have l0 : ∀ sK3 sK1 sK2 sK0 : G, (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z x y w]

theorem Equation4512_41964_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41964 : Equation41964 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41964 X1 X2 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41964 X0 X1 X2 X1]
  have l1 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41964 sK0 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ sK2) = (sK2 ◇ (X1 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [h41964 sK1 sK2 X1 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l3 : ∀ X2 X3 X0 X1 X4 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X3 X0 X1 X4
    conv => enter [1]; rw [h41964 X2 X3 (X0 ◇ X1) X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h41964 X0 (X1 ◇ X2) X3 X4]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X4)))]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l4 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X4]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2 X0 X0]
    conv => enter [1]; rw [← l3 X0 X1 X2 X0 (X2 ◇ X0)]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ sK2) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK1 X0]
    conv => enter [1]; rw [← l0 X0 sK2 sK1 (sK1 ◇ sK2)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0 X0]
    conv => enter [1]; rw [← l0 X0 sK0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [← l6 X0 X1 sK2]
    conv => enter [1]; rw [← l9 sK1 sK2 X0 X1]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l11 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation41965 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41965 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z x y]

theorem Equation4512_41965_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41965 : Equation41965 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ X2) = (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41965 (X0 ◇ (X1 ◇ X0)) X2 X1]
    conv => enter [1, 2, 2]; rw [← h41965 X0 (X0 ◇ (X1 ◇ X0)) X1]
  have l1 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h41965 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41965 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l2 X2 X3 X0 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [← l1 X0 X1 X3 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l6 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = (X0 ◇ (X1 ◇ X3)) := by
    intro X1 X3 X0
    conv => enter [1]; rw [l3 X1 X3 X1 X0]
    conv => enter [1]; rw [l4 X3 X1 X0 X1]
  have l7 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l5 X2 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l8 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X1 ◇ (X0 ◇ X2)) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l7 X2 X1 X0]
    conv => enter [1]; rw [← l6 X1 (X0 ◇ X2) X0]
  have l9 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = (X0 ◇ X2) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l8 X2 X1 X0]
    conv => enter [1]; rw [← l6 X0 X2 X1]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X2]
    conv => enter [1]; rw [l9 X2 X1 X0]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l6 X1 X0 X0]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X0]
    conv => enter [1]; rw [l12 X0 X1 X2]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l13 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l14 y z x]

@[equational_result]
theorem Equation41_implies_Equation41968 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41968 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK3 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK3 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41968_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41968 : Equation41968 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41968 X0 X1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41968 X1 X2 (sK0 ◇ sK0) (sK0 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41968 X1 X2 X3 (X0 ◇ (X3 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41968 X0 X1 X3 X1]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h41968 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X2 ◇ X3))) X4]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l4 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X2 ◇ X3)) X4]
  have l6 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l2 X1 X2 sK0 X0]
    conv => enter [1]; rw [← l3 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) X2 (sK0 ◇ sK0) X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l1 X0 X1 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK0 ◇ sK0)) X1 (sK0 ◇ sK0) X0]
  have l8 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h41968 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l3 (sK1 ◇ sK2) X1 sK1 X0]
  have l9 : ∀ X0 X1 X4 : G, ((X0 ◇ X1) ◇ X4) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l5 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← l3 X4 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l10 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l6 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ X0) X2]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l7 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X1]
  have l12 : ∀ X4 X1 sK1 sK2 : G, (X4 ◇ X1) = ((sK1 ◇ sK2) ◇ X4) := by
    intro X4 X1 sK1 sK2
    conv => enter [1]; rw [← l9 X4 X1 X4]
    conv => enter [1]; rw [l8 (X4 ◇ X1) X4 sK1 sK2]
  have l13 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X2) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X2))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l10 X1 X2 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 X2]
  have l14 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ X1) = (sK0 ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l11 X0 X1 sK0]
    conv => enter [1, 2]; rw [l8 (sK0 ◇ sK0) X1 sK1 sK2]
  have l15 : ∀ X1 X2 sK0 : G, (X1 ◇ X2) = (X2 ◇ sK0) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l13 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l3 X2 sK0 (sK0 ◇ sK0) X1]
  have l16 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ X1) = ((sK1 ◇ sK2) ◇ sK0) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l14 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 sK0 ((sK1 ◇ sK2) ◇ X1) sK1 sK2]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l16 X0 X1 X0 X0 sK0]
    conv => enter [1]; rw [l15 (X0 ◇ X0) sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l17 y z x]

@[equational_result]
theorem Equation41_implies_Equation41969 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41969 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK1)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41969_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41969 : Equation41969 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X3 X4 X2 : G, ((X0 ◇ X1) ◇ X3) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h41969 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l1 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41969 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l2 : ∀ X2 X4 X0 : G, (X2 ◇ X4) = (X4 ◇ (X2 ◇ X0)) := by
    intro X2 X4 X0
    conv => enter [1]; rw [l1 X2 X4 X0 X2 X2]
    conv => enter [1, 2]; rw [← h41969 X2 X0 X2 X2]
  have l3 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = (X0 ◇ (X1 ◇ X3)) := by
    intro X3 X4 X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X3 X4 X2]
    conv => enter [1]; rw [← h4512 X0 X1 X3]
  have l4 : ∀ X1 X0 X3 X4 X2 : G, (X1 ◇ X0) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 X3 X4 X2
    conv => enter [1]; rw [l2 X1 X0 X3]
    conv => enter [1]; rw [← l3 X3 X4 X0 X1 X2]
  have l5 : ∀ X1 X0 X4 X3 : G, (X1 ◇ X0) = (X4 ◇ X3) := by
    intro X1 X0 X4 X3
    conv => enter [1]; rw [l4 X1 X0 X3 X4 X1]
    conv => enter [1]; rw [← l2 X4 X3 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 sK1 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation41971 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41971 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ (sK0 ◇ sK3))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK3)) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 (sK0 ◇ sK3)]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK3))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0 sK3]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41971_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41971 : Equation41971 G) : Equation41 G := by
  have l0 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41971 sK0 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 X1 X0 sK2 : G, (sK1 ◇ X1) = (X1 ◇ (X0 ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 X1 X0 sK2
    conv => enter [1]; rw [h41971 sK1 X1 X0 sK2]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK2 X0]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41971 X2 X3 (X1 ◇ X2) X0]
    conv => enter [1, 2]; rw [← h41971 X0 (X1 ◇ X2) X2 X1]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X2))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [h41971 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ X2))) X4]
  have l4 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X2)) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ X2)) X4]
  have l5 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (sK1 ◇ X1) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l2 X0 X1 X0 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l1 sK1 X1 X0 X0]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 X1 X0]
  have l7 : ∀ X0 X1 X4 : G, ((X0 ◇ X1) ◇ X4) = (X4 ◇ X1) := by
    intro X0 X1 X4
    conv => enter [1]; rw [l4 X0 X1 X4 X0 X0]
    conv => enter [1]; rw [← l2 X4 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X4 X1 sK1 : G, (X4 ◇ X1) = (sK1 ◇ X4) := by
    intro X4 X1 sK1
    conv => enter [1]; rw [← l7 X4 X1 X4]
    conv => enter [1]; rw [l5 (X4 ◇ X1) X4 sK1]
  have l9 : ∀ X4 X1 sK0 : G, (X4 ◇ X1) = (sK0 ◇ X4) := by
    intro X4 X1 sK0
    conv => enter [1]; rw [l8 X4 X1 X4]
    conv => enter [1]; rw [l6 X4 X4 sK0]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

@[equational_result]
theorem Equation41_implies_Equation41972 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41972 G := by
  have l0 : ∀ sK3 sK1 sK0 sK2 : G, (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK3 sK1 sK0 sK2
    conv => enter [1]; rw [← h41 sK3 sK3 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l1 sK1 sK0 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK3 sK1 : G, (sK0 ◇ sK0) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK3 sK1
    conv => enter [1]; rw [h41 sK0 sK3 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK0]
  have l5 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK3 sK1]
  intro x y z w
  conv => enter [1]; rw [l5 x y z w]
  conv => enter [1]; rw [l0 z x w y]

theorem Equation4512_41972_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41972 : Equation41972 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ X2) = (X2 ◇ (X3 ◇ (X0 ◇ X1))) := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h41972 X1 X2 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2, 2]; rw [← h41972 X0 X1 (X0 ◇ (X1 ◇ X1)) X1]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41972 X2 X3 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41972 (X0 ◇ X0) X1 X2 X0]
  have l2 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ X4) = (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X2 X4 X0 X1 X3
    conv => enter [1]; rw [h41972 X2 X4 (X0 ◇ X1) X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l3 : ∀ X2 X4 X0 : G, (X2 ◇ X4) = (X4 ◇ (X2 ◇ X0)) := by
    intro X2 X4 X0
    conv => enter [1]; rw [l2 X2 X4 X0 X2 X2]
    conv => enter [1, 2]; rw [← h41972 X2 X0 X2 X2]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X2 X3 X1 : G, (X2 ◇ X3) = (X1 ◇ X3) := by
    intro X2 X3 X1
    conv => enter [1]; rw [l4 X2 X3 X2 X1]
    conv => enter [1]; rw [← l0 X1 X3 X2 X2]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l7 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l6 sK0 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation41_implies_Equation41973 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41973 G := by
  have l0 : ∀ sK4 sK2 sK1 sK0 sK3 : G, (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK3 ◇ (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK4 sK2 sK1 sK0 sK3
    conv => enter [1]; rw [← h41 sK4 sK4 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK4 sK3 (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ X2) = (sK2 ◇ sK3) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK2 sK3]
  have l2 : ∀ sK2 sK3 sK1 sK0 : G, (sK2 ◇ sK3) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK3 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 sK3]
    conv => enter [1]; rw [h41 sK2 sK2 (sK1 ◇ sK0)]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 : G, (sK2 ◇ sK3) = (sK4 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK3 sK4 (sK2 ◇ sK3)]
    conv => enter [1, 2]; rw [l2 sK2 sK3 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l3 x y z w u]
  conv => enter [1]; rw [l0 z x w u y]

theorem Equation4512_41973_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41973 : Equation41973 G) : Equation41 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X3) = (X3 ◇ (X0 ◇ X1)) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41973 X2 X3 X1 X0 (X2 ◇ X2)]
    conv => enter [1, 2]; rw [← h41973 X0 X1 X2 X2 X2]
  have l1 : ∀ X2 X5 X0 X1 X3 X4 : G, (X2 ◇ X5) = (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))) := by
    intro X2 X5 X0 X1 X3 X4
    conv => enter [1]; rw [h41973 X2 X5 (X0 ◇ X1) X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l2 : ∀ X2 X5 X1 : G, (X2 ◇ X5) = (X1 ◇ X5) := by
    intro X2 X5 X1
    conv => enter [1]; rw [l1 X2 X5 X2 X1 X2 X2]
    conv => enter [1]; rw [← h41973 X1 X5 X2 X2 (X2 ◇ X2)]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l6 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [l2 sK2 sK2 sK1]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ sK2) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [l6 sK1 sK2]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l5 sK1 sK2 X0 sK1]
  have l9 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (X1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l0 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ X1) = (sK1 ◇ sK2) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l9 X0 X1 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X1]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l0 X0 X1 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 X1]
  have l12 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l11 sK1 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l12 y z x]

@[equational_result]
theorem Equation41_implies_Equation41974 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41974 G := by
  intro x y z
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (z ◇ (y ◇ (x ◇ x)))]

theorem Equation4512_41974_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41974 : Equation41974 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h41974 (X0 ◇ X0) X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h41974 X0 (X0 ◇ X0) X1]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41974 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41974 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2 X0]
    conv => enter [1, 2]; rw [← l2 X0 X2 X0 X1]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41974 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41974 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h41974 sK0 (sK0 ◇ sK0) X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41974 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h41974 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l5 sK0 (sK0 ◇ sK0)]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [← l8 sK0 X0]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l6 (sK0 ◇ sK0) sK0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l17 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [← l15 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l18 sK0]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1]; rw [← l16 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l21 sK0 X0]
  have l23 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41974 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK0 (X1 ◇ (X0 ◇ X0))]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h41974 X0 (sK0 ◇ sK0) sK0]
  have l25 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l23 X0 X1 sK0]
    conv => enter [1]; rw [← l24 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l25 y z x]

@[equational_result]
theorem Equation41_implies_Equation41976 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41976 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ (sK0 ◇ sK2))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41976_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41976 : Equation41976 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41976 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41976 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l3 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3)) := by
    intro X0 X1 X3 X2
    conv => enter [1, 1]; rw [h41976 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h41976 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ (X0 ◇ X1)))]
  have l5 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X2)) X3]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0) sK0]
  have l7 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l5 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l8 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l7 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ X3)) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 X3]
    conv => enter [1]; rw [l9 X0 X1 X3 X2]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41976 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l10 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41976 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h41976 X1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l13 sK0 (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ X0)))]
  have l15 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (X1 ◇ X0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l14 X1 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l13 sK0 (X1 ◇ X0)]
  have l16 : ∀ X1 sK0 : G, (X1 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0
    conv => enter [1]; rw [h41976 X1 sK0 X1]
    conv => enter [1]; rw [← l15 X1 sK0 X1]
  have l17 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l1 sK0 (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))]
    conv => enter [1, 2, 2]; rw [← h41976 X0 (sK0 ◇ sK0) X1]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41976 X0 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ ((X1 ◇ ((sK0 ◇ sK0) ◇ X1)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41976 sK0 X0 (X1 ◇ ((sK0 ◇ sK0) ◇ X1))]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK0 X1]
  have l20 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l19 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ X1) (X0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l18 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l22 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l17 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) (X0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l20 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) X1 (X0 ◇ (sK0 ◇ sK0))]
  have l24 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l21 X0 sK0]
    conv => enter [1, 2]; rw [← l13 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l22 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) (X0 ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l23 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h41976 X0 X1 (sK0 ◇ sK0)]
  have l27 : ∀ X0 sK0 : G, (X0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l24 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l25 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← l13 sK0 ((X0 ◇ X1) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l27 X0 sK0]
  have l30 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l28 sK0 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [← l29 sK0 X0]
    conv => enter [1, 2]; rw [← l16 X0 sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 sK0 X0]
    conv => enter [1]; rw [← l11 X0 sK0 (X0 ◇ (sK0 ◇ sK0)) sK0]
  have l33 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l16 X0 sK0]
  have l34 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1, 2]; rw [← l31 X0 sK0]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [← l26 sK0 X0 sK0]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 (sK0 ◇ X0)]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l37 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41976 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l35 sK0 (X1 ◇ (X0 ◇ sK0))]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l36 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))]
    conv => enter [1]; rw [← h41976 X0 (sK0 ◇ sK0) sK0]
  have l39 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l37 X0 X1 sK0]
    conv => enter [1]; rw [← l38 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l39 y z x]

@[equational_result]
theorem Equation41_implies_Equation41977 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41977 G := by
  have l0 : ∀ sK3 sK2 sK1 sK0 : G, (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK3 sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK1 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z y x w]

theorem Equation4512_41977_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41977 : Equation41977 G) : Equation41 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X2 ◇ (X0 ◇ X1)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h41977 X1 X2 X1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h41977 X0 X1 X2 X1]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X4)) = ((X0 ◇ X1) ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ (X0 ◇ X3))) X4]
    conv => enter [1, 1]; rw [← h41977 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X4)) = (X0 ◇ (X1 ◇ X4)) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 X4]
  have l3 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X3))) ◇ X4)) = (X4 ◇ X0) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [l2 X1 X2 X0 X3 X4]
    conv => enter [1]; rw [← l0 X4 X0 X1]
  have l4 : ∀ X4 X0 X1 : G, (X4 ◇ X0) = (X4 ◇ X1) := by
    intro X4 X0 X1
    conv => enter [1]; rw [l0 X4 X0 (X4 ◇ (X0 ◇ (X1 ◇ X4)))]
    conv => enter [1]; rw [l3 X0 X4 X1 X4 X4]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0 (sK0 ◇ (sK0 ◇ (X0 ◇ sK0)))]
    conv => enter [1]; rw [← h41977 X0 sK0 sK0 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l6 y z x]

@[equational_result]
theorem Equation41_implies_Equation41978 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41978 G := by
  have l0 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z y x]

theorem Equation4512_41978_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41978 : Equation41978 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41978 (sK0 ◇ X0) (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 X0]
  have l2 : ∀ X3 X2 X0 X1 : G, (X3 ◇ X2) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))) := by
    intro X3 X2 X0 X1
    conv => enter [1]; rw [h41978 X3 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l3 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
    conv => enter [1]; rw [← l2 X0 (sK0 ◇ sK0) sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l4 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41978 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41978 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h41978 sK0 sK0 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h41978 sK0 sK0 sK0]
    conv => enter [1]; rw [← l7 X0 sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1, 2]; rw [← l9 sK0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41978 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 X0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l15 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l14 sK0 X0]
  have l17 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l14 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0]
  have l19 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41978 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l18 sK0 (X1 ◇ (X1 ◇ X0))]
  have l20 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l19 X0 X1 sK0]
    conv => enter [1]; rw [← l14 sK0 X1]
  intro x y z
  conv => enter [1]; rw [← l20 y z x]

@[equational_result]
theorem Equation41_implies_Equation41980 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41980 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l1 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l4 x y z]
  conv => enter [1]; rw [l0 z y]

theorem Equation4512_41980_implies_Equation41 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41980 : Equation41980 G) : Equation41 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41980 X0 X1 X0]
    conv => enter [1]; rw [← h41980 X2 X1 X0]
  have l1 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ X1) X0]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X1 ◇ (sK0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41980 X0 X1 sK0]
    conv => enter [1, 2, 2, 2]; rw [l0 X1 sK0 sK0]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ sK0)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0]
  have l5 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← l1 sK0 (X1 ◇ (sK0 ◇ sK0)) X1]
  have l6 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l5 X0 X1 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 X1]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (sK0 ◇ sK0) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK0]
    conv => enter [1]; rw [← l4 sK0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ sK2) = (X0 ◇ (X1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 sK2]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK2) sK0]
  intro x y z
  conv => enter [1]; rw [← l9 y z x]

@[equational_result]
theorem Equation41_implies_Equation41981 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation41981 G := by
  have l0 : ∀ sK3 sK2 sK0 : G, (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK3 sK2 sK0
    conv => enter [1]; rw [← h41 sK3 sK3 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [h41 sK3 sK2 (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0)))]
  have l1 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ X2) = (sK1 ◇ sK2) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK1 sK2]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h41 sK1 sK1 sK2]
    conv => enter [1]; rw [h41 sK1 sK2 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ sK2) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK2 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK2) = (sK3 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK3 (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l3 sK1 sK2 sK0]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]
  conv => enter [1]; rw [l0 z y w]

end Semigroup5
