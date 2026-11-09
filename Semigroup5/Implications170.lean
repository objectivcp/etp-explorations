import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_41601_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41601 : Equation41601 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41601 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41601 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ X0)))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41601 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41601 X0 X0 X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h41601 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0 sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l5 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation312_implies_Equation41618 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41618 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation4512_41618_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41618 : Equation41618 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h41618 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h41618 X0 (X0 ◇ (X0 ◇ X0))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41618 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0)))) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41618 X0 sK0]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41618 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h41618 X0 X0]
    conv => enter [1]; rw [← l8 X1 X0]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK0 ◇ sK0) sK0]
  have l12 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41618 ((sK0 ◇ sK0) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l2 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l12 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l16 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l18 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l15 X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l19 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l7 sK0 sK0]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l18 X0 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l23 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l21 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) sK0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← l24 sK1 sK0]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l17 sK1 sK0]
  have l27 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h41618 (sK1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l26 sK0 sK1]
  have l28 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l27 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← l17 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]

@[equational_result]
theorem Equation312_implies_Equation41638 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41638 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [h312 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41638_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41638 : Equation41638 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h41638 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41638 (sK0 ◇ sK0) X0 X0]
    conv => enter [1, 2]; rw [← h41638 sK0 X0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41638 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41638 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41638 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) sK0 sK0]
    conv => enter [1]; rw [← l6 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation312_implies_Equation41655 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41655 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h312 sK0 sK2]
    conv => enter [1, 2]; rw [h312 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41655_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41655 : Equation41655 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h41655 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41655 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41655 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41655 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41655 X0 X0 X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 sK0]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l5 (sK0 ◇ sK0) sK0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1, 2]; rw [← l1 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation312_implies_Equation41672 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41672 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h312 sK0 sK2]
    conv => enter [1, 2]; rw [h312 sK0 sK1]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41672_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41672 : Equation41672 G) : Equation312 G := by
  have l0 : ∀ sK0 X2 X0 X1 : G, (sK0 ◇ sK0) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X2 X0 X1
    conv => enter [1]; rw [h41672 sK0 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h41672 sK0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0)))]
  have l2 : ∀ sK0 X0 X1 X2 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation312_implies_Equation41689 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41689 G := by
  have l0 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h312 sK0 sK2]
    conv => enter [1, 2]; rw [h312 sK0 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h312 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_41689_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41689 : Equation41689 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41689 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41689 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41689 X0 X0 X0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2]; rw [← h41689 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← l5 sK0 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0]
  have l9 : ∀ sK1 sK0 X0 X1 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [← l5 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 X0 X1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation312_implies_Equation41706 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation41706 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ sK1) = (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h312 sK1 sK3]
    conv => enter [1, 2]; rw [h312 sK1 sK0]
  have l1 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h312 sK1 sK2]
    conv => enter [1, 2]; rw [l0 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l1 x y z w]

theorem Equation4512_41706_implies_Equation312 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41706 : Equation41706 G) : Equation312 G := by
  have l0 : ∀ sK0 X0 X1 X2 X3 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 X2 X3
    conv => enter [1]; rw [h41706 sK0 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (sK0 ◇ sK0)))]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41706 sK0 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation313_4512_implies_Equation319 (G : Type*) [Magma G] (h313 : Equation313 G) (h4512 : Equation4512 G) : Equation319 G := by
  have l0 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 sK1]
    conv => enter [1]; rw [h313 sK2 sK2]
    conv => enter [1, 2]; rw [h313 sK2 sK1]
  have l1 : ∀ sK2 sK1 : G, (sK2 ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [h313 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l0 sK1 sK2]
  have l2 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK1)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h313 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h313 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h313 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h313 X0 (sK0 ◇ sK0)]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [l4 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h313 sK0 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation319_implies_Equation313 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h319 x y x]

@[equational_result]
theorem Equation314_implies_Equation321 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation321 G := by
  have l0 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l0 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l2 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l1 sK1 sK3]
    conv => enter [1]; rw [h314 sK3 X0 sK0]
  intro x y z w
  conv => enter [1]; rw [l2 x y z w]

@[equational_result]
theorem Equation321_implies_Equation314 (G : Type*) [Magma G] (h321 : Equation321 G) : Equation314 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h321 X0 X0 sK0 sK0]
    conv => enter [1]; rw [← h321 sK0 X0 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h321 sK0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation315_4512_implies_Equation3281 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3281 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK1 ◇ sK0) sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation3281_4512_implies_Equation315 (G : Type*) [Magma G] (h3281 : Equation3281 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3281 X0 X1]
    conv => enter [1]; rw [← h3281 (X1 ◇ X0) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3281 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← h3281 sK0 sK1]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h3281 sK0 sK0]
    conv => enter [1]; rw [← h3281 (sK0 ◇ sK0) sK0]
  have l4 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3281 (sK1 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h3281 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3281 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [← h3281 (sK1 ◇ sK0) sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3281 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))))) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h3281 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) sK1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h3281 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 sK0]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h3281 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3281 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l13 sK0 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1, 2]; rw [← l3 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3281 sK0 sK0]
    conv => enter [1]; rw [← l17 sK0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l18 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l20 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3281 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l22 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h3281 X0 X1]
    conv => enter [1]; rw [l20 X0 sK0]
  have l23 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l22 X1 X0 sK0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l24 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h3281 X0 X0]
    conv => enter [1]; rw [← l1 X0 X0]
  have l25 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l24 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l25 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l27 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1]; rw [l23 X0 X1 sK0]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [← l27 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l28 x y]

theorem Equation315_4512_implies_Equation3284 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3284 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ sK0) sK1]
  have l3 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK0]
  have l7 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [← l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l9 x y z]

theorem Equation3284_4512_implies_Equation315 (G : Type*) [Magma G] (h3284 : Equation3284 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h3284 sK0 X0 sK0]
    conv => enter [1]; rw [← h3284 (sK0 ◇ sK0) X0 X0]
  have l1 : ∀ X0 sK0 X1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l0 X0 sK0]
    conv => enter [1]; rw [← l0 X1 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h3284 sK0 X0 sK0]
    conv => enter [1, 2]; rw [l0 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h3284 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0 X0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 sK0]
    conv => enter [1, 2]; rw [← h3284 sK0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3284 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK0) sK0 X0]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h3284 X1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h3284 X0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 sK0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l11 X1 sK0]
    conv => enter [1]; rw [l9 X1 sK0 X0]
  have l13 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ X2)) = ((X0 ◇ X0) ◇ X2) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X1 ◇ X0) X2]
    conv => enter [1, 1]; rw [← l9 X0 sK0 X1]
  have l14 : ∀ sK0 X1 X0 X2 : G, ((sK0 ◇ sK0) ◇ ((X1 ◇ X0) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X1 X0 X2
    conv => enter [1]; rw [l13 sK0 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 X0 X2]
  have l15 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [l12 sK0 X2 (sK0 ◇ X0)]
    conv => enter [1]; rw [l14 sK0 sK0 X0 X2]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation315_4512_implies_Equation3296 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation3296 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h315 X1 X0]
    conv => enter [1]; rw [h315 X1 X2]
  have l1 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2, 2]; rw [← h315 sK0 sK2]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK1]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
    conv => enter [1]; rw [l5 sK1 sK0 sK2]
  have l7 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 1, 2]; rw [h315 sK0 sK2]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l8 X0 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l8 X0 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l12 X0 X1 sK0]
    conv => enter [1]; rw [l9 X0 X1 sK0]
  have l14 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
  have l15 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [← l14 sK1 sK2 sK0 X0]
  have l16 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK0)) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l0 X0 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [← h315 (sK2 ◇ (sK2 ◇ sK0)) sK1]
  have l17 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l16 X0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [l8 (sK2 ◇ (sK2 ◇ sK0)) sK0]
  have l18 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l17 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK1 sK0 (sK2 ◇ (sK2 ◇ sK0)) sK2]
  have l19 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l18 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l15 sK0 (sK2 ◇ (sK2 ◇ sK0)) sK1 sK2]
  have l20 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [h315 sK0 sK2]
    conv => enter [1]; rw [← l19 X0 sK1 sK2 sK0]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l20 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [← l21 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l23 x y z]

theorem Equation3296_4512_implies_Equation315 (G : Type*) [Magma G] (h3296 : Equation3296 G) (h4512 : Equation4512 G) : Equation315 G := by
  have l0 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h3296 (sK1 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [← h3296 sK0 X1 sK1]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h3296 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l0 sK0 sK0 X0 X1]
  have l2 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2]; rw [h3296 sK0 X1 sK0]
    conv => enter [1]; rw [← h3296 (sK0 ◇ (sK0 ◇ sK0)) X0 X1]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l2 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [l1 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l3 X0 X1 sK0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0 sK0 sK0]
    conv => enter [1]; rw [← l4 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h3296 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0]
  have l7 : ∀ sK0 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0 sK1
    conv => enter [1, 1]; rw [h3296 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h3296 X0 X1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h3296 X0 X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l7 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) X0 sK1]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l10 X0 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 X0 (sK0 ◇ sK0) X0]
  have l12 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [← h3296 X0 X1 X2]
    conv => enter [1]; rw [l11 X0 sK0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h3296 X0 X1 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l8 X0 (X0 ◇ X0) X0]
  have l14 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l13 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l16 : ∀ sK0 X2 X0 : G, ((sK0 ◇ sK0) ◇ X2) = (X0 ◇ (X0 ◇ X2)) := by
    intro sK0 X2 X0
    conv => enter [1]; rw [← l12 sK0 X0 X2 sK0]
    conv => enter [1]; rw [← l15 X0 X2 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l16 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation315_implies_Equation41584 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation41584 G := by
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
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h315 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation4512_41584_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41584 : Equation41584 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h41584 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41584 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41584 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l6 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41584 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l7 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l8 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l12 sK0]
  have l14 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l14 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l17 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = (X0 ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41584 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) X0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK0 X0]
  have l18 : ∀ X0 sK0 X1 : G, (X0 ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h4512 X0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l2 sK0 X0]
  have l19 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l18 X0 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) X1]
  have l20 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ X1)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l19 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK0 X1]
  have l22 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK0 (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← l21 sK0 (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ (sK0 ◇ sK0)) X0]
  have l24 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l23 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) (sK0 ◇ sK0)]
  have l25 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 ((X0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 (sK0 ◇ sK0)]
  have l27 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l14 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((X0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l27 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l16 sK0 (X0 ◇ sK0)]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41584 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l32 sK0 X0]
  have l34 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l32 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0)) X1]
  have l35 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l34 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l36 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [l33 sK0 X0]
    conv => enter [1, 2]; rw [← l13 sK0]
  have l37 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l36 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l38 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK0 (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))))]
  have l39 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l38 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l37 sK0 ((sK0 ◇ sK0) ◇ X0) X0]
  have l40 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l39 X0 sK0]
    conv => enter [1]; rw [← l35 sK0 ((sK0 ◇ sK0) ◇ X0) X0]
  have l41 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l40 X0 sK0]
    conv => enter [1]; rw [← l37 sK0 X0 (sK0 ◇ sK0)]
  have l42 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l4 X1 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2, 2, 2]; rw [l41 (X0 ◇ X1) sK0]
  have l43 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l42 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))))]
  have l44 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l43 X1 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l37 sK0 (X0 ◇ X1) X1]
  have l45 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l44 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l37 sK0 (X0 ◇ X1) X1]
  have l46 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l45 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l37 sK0 (X0 ◇ X1) X0]
  have l47 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l46 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l37 sK0 (X0 ◇ X1) X1]
  have l48 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l47 X1 X0 sK0]
    conv => enter [1]; rw [← l37 sK0 (X0 ◇ X1) X0]
  have l49 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l48 X1 sK0 X0]
    conv => enter [1]; rw [l41 X1 sK0]
  have l50 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [l48 X1 sK0 X0]
  have l51 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l50 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
  have l52 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l51 X1 X2 sK0 X1]
    conv => enter [1]; rw [l49 sK0 (X1 ◇ X1) X2]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK0]
    conv => enter [1]; rw [← l53 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l54 x y]

theorem Equation315_4512_implies_Equation41587 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41587 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ sK0) sK0]
  have l3 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0 sK2]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [← l5 sK0 sK2]
  have l7 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h315 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← h315 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l8 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [← l7 sK1 sK0 sK2]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l11 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [l10 sK2 sK0]
  have l12 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l9 X0 sK0]
  have l13 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l8 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 sK0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l14 sK0 X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 sK0]
    conv => enter [1]; rw [l12 X0 X1 sK0]
  have l17 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l13 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
  have l18 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l16 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l17 sK1 sK0 sK2 X0]
  have l19 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [l19 sK2 sK0]
  have l21 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l20 sK0 sK2]
  have l22 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l2 sK0 sK2]
    conv => enter [1]; rw [← l21 sK0 sK2]
  have l23 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l22 sK0 sK2]
  have l24 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l25 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l24 sK1 sK0 sK2]
    conv => enter [1]; rw [← l18 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1 sK2]
  have l26 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2]
    conv => enter [1]; rw [← l25 sK1 sK0 sK2]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK0]
    conv => enter [1]; rw [l26 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l23 sK0 sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [l23 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

theorem Equation4512_41587_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41587 : Equation41587 G) : Equation315 G := by
  have l0 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h41587 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 sK1]
  have l1 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h41587 sK0 X1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41587 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ X0)))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41587 X0 X0 X0]
  have l4 : ∀ sK1 X0 sK0 : G, (sK1 ◇ sK1) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41587 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41587 sK0 X0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ sK0) sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l7 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41587 (sK1 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l5 sK0 (sK1 ◇ sK0) sK1]
  have l10 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l5 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 sK0 sK0 sK0]
  have l12 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l13 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l8 sK0 (X0 ◇ sK0)]
  have l16 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h4512 X0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← l9 sK1 sK0 X0]
  have l17 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l16 X0 sK1 sK0 X1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X1]
  have l18 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l17 X0 sK1 sK0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X1]
  have l19 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1, 2]; rw [l12 sK0 X1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l18 sK1 sK0 X1 X0]
  have l20 : ∀ sK0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l12 sK0 X1 sK0]
    conv => enter [1]; rw [l19 sK0 sK0 X1 sK1]
  have l21 : ∀ sK1 sK0 X1 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ (((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1, 1]; rw [h41587 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) X1]
  have l22 : ∀ sK1 sK0 X1 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l21 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l23 : ∀ sK1 sK0 X1 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l22 sK1 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l24 : ∀ sK1 sK0 X1 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l23 sK1 sK0 X1 sK1]
    conv => enter [1]; rw [← l14 (sK1 ◇ sK0) ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1) sK1]
  have l25 : ∀ sK1 sK0 X1 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l24 sK1 sK0 X1]
    conv => enter [1]; rw [← l20 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1) sK1]
  have l26 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [l25 sK1 sK0 X1]
  have l27 : ∀ sK0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 sK1
    conv => enter [1]; rw [l20 sK0 X1 sK1]
    conv => enter [1]; rw [l26 sK1 sK0 X1]
  have l28 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l27 sK0 sK1 sK1]
  have l29 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← l28 sK1 sK0]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l30 sK0 sK1 sK0]
    conv => enter [1]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l31 y x]

theorem Equation315_4512_implies_Equation41609 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41609 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← h315 X1 X0]
    conv => enter [1]; rw [h315 X1 X2]
  have l1 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1, 2]; rw [h315 sK0 sK2]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l2 sK0]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2, 2]; rw [← l1 sK0 sK2]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l4 sK1 sK0 sK2]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1]
  have l7 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l1 sK0 sK2]
    conv => enter [1]; rw [l6 sK1 sK0 sK2]
  have l8 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1, 1, 2]; rw [l1 sK0 sK2]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l9 X0 sK0]
  have l11 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [l9 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l9 X0 sK0]
  have l13 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l12 sK0 X0 X1]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l13 X0 X1 sK0]
    conv => enter [1]; rw [l10 X0 X1 sK0]
  have l15 : ∀ sK1 sK0 sK2 X0 : G, ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 sK2 X0
    conv => enter [1, 1]; rw [l11 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
  have l16 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK2 X0]
  have l17 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) = (sK1 ◇ ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l0 X0 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← h315 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1]
  have l18 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l17 X0 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l9 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l19 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l18 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [l8 sK1 sK0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK2]
  have l20 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l19 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK1 sK2]
  have l21 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [← l20 X0 sK1 sK0 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) sK0]
  have l23 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l7 sK1 sK0 sK2]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [← l23 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l24 x y z]

theorem Equation4512_41609_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41609 : Equation41609 G) : Equation315 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41609 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ (X0 ◇ sK0))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41609 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41609 X0 X0 X0]
  have l3 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h41609 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 X0 sK0 sK0]
    conv => enter [1, 2]; rw [← h41609 sK0 sK0 sK0]
  have l5 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l7 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ (X0 ◇ sK0))]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK0 X0]
    conv => enter [1]; rw [← l6 X0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation315_4512_implies_Equation41624 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41624 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h315 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h315 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [h315 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l3 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [l3 sK2 sK0]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← l4 sK0 sK2]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l5 sK0 sK2]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← h315 X0 sK0]
  have l8 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l9 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l8 sK2 sK0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK2 ◇ sK0))]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0]
    conv => enter [1, 2]; rw [h315 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l11 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [l10 sK2 sK0 sK1]
  have l12 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [l12 sK2 sK0 sK1]
  have l14 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))))]
  have l15 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l14 sK0 sK2 sK1]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← l15 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

theorem Equation4512_41624_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41624 : Equation41624 G) : Equation315 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ X2) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [h41624 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41624 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h41624 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ sK0)]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) = ((X0 ◇ X0) ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X2 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← h41624 X0 X1 X2]
  have l4 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ (X0 ◇ X3)) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
    conv => enter [1]; rw [← h4512 X0 X0 X3]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ sK0)]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l4 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X0)) X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ X0) X3]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ X3)) = (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41624 (sK0 ◇ sK0) X0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l6 sK0 sK0]
    conv => enter [1]; rw [← l10 sK0 sK0]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41624 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41624 X0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l14 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41624 X0 (sK0 ◇ sK0) X0]
  have l16 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ ((X0 ◇ sK0) ◇ (X0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l0 sK0 X1 (X0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l15 (X0 ◇ sK0) sK0]
  have l17 : ∀ sK0 X1 X0 : G, (sK0 ◇ sK0) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ (X0 ◇ sK0))))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l16 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK0 (X0 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0 sK0 X0]
    conv => enter [1]; rw [← l9 X0 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation315_implies_Equation41631 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation41631 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h315 sK0 sK1]
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation4512_41631_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41631 : Equation41631 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41631 (sK0 ◇ X0) sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41631 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h41631 X0 X1]
    conv => enter [1]; rw [← h41631 (X1 ◇ X0) X1]
  have l5 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))))) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l1 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h41631 X0 sK0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l5 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ X0))]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l3 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h41631 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l11 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ X0)))]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l11 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ X0)]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ (sK0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 X0 (sK0 ◇ X0)]
    conv => enter [1]; rw [l13 sK0 X0]
  have l16 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l14 sK1 sK0 X0]
    conv => enter [1]; rw [l1 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ X0))]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (X0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l18 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l16 sK1 sK0 X0]
    conv => enter [1, 2, 2]; rw [l0 sK0 X0]
  have l19 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l18 sK1 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))]
  have l21 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h41631 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l22 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l21 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [l0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l24 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l8 (sK0 ◇ sK0) sK0]
  have l27 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [← l17 sK0 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [← l27 sK0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1, 2]; rw [← l28 sK0]
  have l30 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l28 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l29 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
  have l33 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l34 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l33 sK1 sK0 X0]
  have l35 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h41631 X0 X1]
    conv => enter [1]; rw [l8 X0 sK0]
  have l36 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41631 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 X0 sK0]
  have l37 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l8 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
  have l38 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [← l37 X0 X1 sK0]
  have l39 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l36 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 (X0 ◇ X0)]
  have l40 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l35 X1 X0 sK0]
    conv => enter [1]; rw [← l30 sK0 X0]
  have l41 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l38 sK0 X0 X1]
  have l42 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l41 X0 X1 sK0]
    conv => enter [1]; rw [← l30 sK0 (X0 ◇ X1)]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2, 2]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← h41631 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) (sK1 ◇ sK0)]
  have l44 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l43 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l45 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1]; rw [l42 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1, 2]; rw [l42 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l52 : ∀ X0 X1 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [l39 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l53 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l52 X0 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l54 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← h41631 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
  have l55 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0)) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0) (sK1 ◇ (sK0 ◇ sK0))]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l56 sK0 sK1]
    conv => enter [1]; rw [l20 sK1 sK0 (sK1 ◇ (sK0 ◇ sK0))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l34 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l30 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l59 sK1 sK0]
  have l61 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l61 sK1 sK0]
  have l63 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1, 2]; rw [← l26 sK0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l63 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l65 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l67 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l68 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) = (((sK0 ◇ sK0) ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2, 2, 2]; rw [l30 sK0 X0]
    conv => enter [1]; rw [← h41631 ((sK0 ◇ sK0) ◇ X0) (sK0 ◇ sK0)]
  have l69 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l68 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 ((sK0 ◇ sK0) ◇ X0)]
  have l70 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l69 sK0 X0]
  have l71 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l40 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l70 sK0 X0]
  have l72 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1, 1]; rw [← h41631 (sK1 ◇ sK0) sK1]
  have l73 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [← l72 sK1 sK0 X0]
  have l74 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l73 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l75 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [← l74 sK1 sK0 X0]
  have l76 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l75 sK1 sK0 X0]
    conv => enter [1]; rw [l42 (sK1 ◇ sK0) X0 sK0]
  have l77 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l22 sK0 X0 sK1]
    conv => enter [1]; rw [l76 sK1 sK0 X0]
  have l78 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l67 sK0 X0 sK1]
    conv => enter [1]; rw [l77 sK1 sK0 X0]
  have l79 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41631 ((sK1 ◇ sK0) ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l78 sK0 X0 sK1]
  have l80 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (((sK1 ◇ sK0) ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l40 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l79 sK1 sK0 X0]
  have l81 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l80 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) X0 ((sK1 ◇ sK0) ◇ X0)]
  have l82 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l81 sK0 X0 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0) X0]
  have l83 : ∀ X0 sK1 sK0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41631 (X0 ◇ X0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l82 sK0 X0 sK1]
  have l84 : ∀ X0 sK0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l83 X0 sK1 sK0]
    conv => enter [1]; rw [l42 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) sK0]
  have l85 : ∀ X0 sK1 sK0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l84 X0 sK0 sK1]
    conv => enter [1]; rw [← l53 (sK1 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) sK0]
  have l86 : ∀ X0 sK0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l85 X0 sK1 sK0]
    conv => enter [1]; rw [l42 (sK1 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) sK0]
  have l87 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l78 sK0 X0 sK0]
    conv => enter [1]; rw [← l86 X0 sK0 sK0]
  have l88 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l87 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l89 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l88 sK0 X0]
    conv => enter [1]; rw [← l7 X0 X0]
  have l90 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l30 sK0 X0]
    conv => enter [1]; rw [l89 sK0 X0]
  have l91 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l90 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l92 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l91 sK0 X0 X1]
  have l93 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [l92 X0 X1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l94 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h41631 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l32 sK0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))]
    conv => enter [1, 2]; rw [← h41631 X0 (sK0 ◇ sK0)]
  have l95 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l94 X0 sK0]
  have l96 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l82 sK0 X0 sK1]
    conv => enter [1]; rw [l95 sK1 sK0 X0]
  have l97 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h41631 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l67 X0 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X0))) sK1]
    conv => enter [1, 2]; rw [← h41631 X0 (X0 ◇ X0)]
  have l98 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l96 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l99 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l98 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l7 X0 X1]
  have l100 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0)))) := by
    intro X0 sK1
    conv => enter [1]; rw [h41631 (X0 ◇ X0) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l97 X0 sK1]
  have l101 : ∀ X0 sK0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l100 X0 sK1]
    conv => enter [1]; rw [l93 sK1 (X0 ◇ X0) sK0]
  have l102 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro X0 sK1
    conv => enter [1]; rw [l101 X0 X0 sK1]
    conv => enter [1]; rw [← l42 sK1 (X0 ◇ X0) X0]
  have l103 : ∀ X0 sK0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l102 X0 sK1]
    conv => enter [1]; rw [← l99 sK0 sK1 X0 sK1]
  have l104 : ∀ X0 sK1 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [l103 X0 X0 sK1]
    conv => enter [1]; rw [← l42 sK1 X0 X0]
  have l105 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l104 X0 sK1]
  have l106 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l93 X0 X0 sK0]
    conv => enter [1]; rw [l105 X0 sK1]
  have l107 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l71 sK0 X0]
    conv => enter [1]; rw [l106 sK0 X0 sK1]
  have l108 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l107 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l109 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l108 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l109 x y]

theorem Equation315_4512_implies_Equation41634 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41634 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h315 (sK1 ◇ (sK2 ◇ sK0)) (sK1 ◇ (sK2 ◇ sK0))]
    conv => enter [1, 2]; rw [h315 (sK1 ◇ (sK2 ◇ sK0)) sK1]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ sK0) sK1]
  have l4 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [l4 sK2 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) (sK1 ◇ (sK2 ◇ sK0))]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK2 sK0]
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 sK0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [h315 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l11 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1]; rw [h315 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [h315 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l13 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l12 X0 sK0]
  have l14 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [l12 (sK2 ◇ sK0) sK0]
  have l15 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) sK0]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l12 X0 sK0]
  have l17 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l16 sK0 X0 X1]
  have l18 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l17 X0 X1 sK0]
    conv => enter [1]; rw [l13 X0 X1 sK0]
  have l19 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l14 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ sK0) X0]
  have l20 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l18 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [← l19 sK1 sK2 sK0 X0]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l11 sK1 sK2 sK0]
    conv => enter [1]; rw [← l20 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) sK1 sK2]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK0]
    conv => enter [1]; rw [l18 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l23 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l15 sK1 sK2 sK0]
    conv => enter [1]; rw [← l22 sK1 sK2 sK0]
  have l24 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [← l23 sK1 sK2 sK0]
  have l25 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK0 ◇ sK0)]
  have l26 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l25 sK2 sK0]
  have l27 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l26 sK1 sK2 sK0]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK0]
    conv => enter [1]; rw [← l27 sK0 sK2 sK1]
  have l29 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l28 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l29 x y z]
  conv => enter [1]; rw [l24 y z x]

theorem Equation4512_41634_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41634 : Equation41634 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41634 sK0 X0 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41634 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41634 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41634 (sK0 ◇ sK0) X0 X0]
    conv => enter [1, 2]; rw [← h41634 sK0 X0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h41634 X1 (X0 ◇ X1) X0]
    conv => enter [1, 2, 2]; rw [l2 (X0 ◇ X1) sK0]
  have l8 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l7 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l8 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l9 X1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l6 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) X1]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l10 X1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l6 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) X0]
  have l12 : ∀ X1 X0 sK0 : G, (X1 ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1)))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l11 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l6 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) X1]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l12 X1 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) X0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l6 sK0 (X0 ◇ X1) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l13 X1 sK0 X0]
  have l15 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 sK0]
    conv => enter [1]; rw [← l6 sK0 X0 (sK0 ◇ sK0)]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [l15 X1 sK0]
  have l17 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [← l14 sK0 X0 X1]
  have l18 : ∀ sK0 X0 X1 X2 : G, ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
    conv => enter [1]; rw [← l17 X1 X2 sK0 X0]
  have l19 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← l16 sK0 (sK0 ◇ X1) X2]
    conv => enter [1]; rw [l18 sK0 sK0 X1 X2]
  have l20 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l19 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l20 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l21 x y]

theorem Equation315_4512_implies_Equation41642 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41642 G := by
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
  have l3 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 2]; rw [← h315 (sK1 ◇ sK0) sK2]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l4 sK2 sK1 sK0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l6 X0 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK0]
  have l9 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [l6 (sK2 ◇ (sK1 ◇ sK0)) sK0]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l6 X0 sK0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l10 sK0 X0 X1]
  have l12 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l11 X0 X1 sK0]
    conv => enter [1]; rw [l7 X0 X1 sK0]
  have l13 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l9 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l14 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l13 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [l12 sK0 (sK2 ◇ (sK1 ◇ sK0)) X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l8 sK1 sK0]
  have l16 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [l12 sK0 sK1 (sK0 ◇ sK0)]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l6 (sK1 ◇ sK0) sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l20 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) X0]
  have l22 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← l14 sK0 sK2 sK0 X0]
    conv => enter [1]; rw [l21 sK0 sK2 sK0 X0]
  have l23 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK2 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [l6 (sK1 ◇ sK0) sK0]
  have l24 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l25 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [l24 sK2 sK1 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK2 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [← l23 sK2 sK1 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← l27 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

theorem Equation4512_41642_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41642 : Equation41642 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41642 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h41642 X0 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41642 X0 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l3 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41642 (X1 ◇ X0) X1 X1]
    conv => enter [1, 2]; rw [← h41642 X0 X1 X1]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41642 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ X0)]
  have l5 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ X0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41642 X0 sK0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X1 ◇ (sK0 ◇ X0))]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l4 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l8 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l2 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l1 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ X0)]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0]
    conv => enter [1, 2]; rw [← l5 (sK0 ◇ sK0) sK0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41642 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [← l9 (sK0 ◇ sK0) sK0]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l12 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l14 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41642 (sK0 ◇ sK0) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l11 sK0 X0]
  have l15 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h41642 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X1]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 X0]
  have l16 : ∀ X0 sK0 X1 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l15 X0 sK0 X1]
    conv => enter [1]; rw [← l13 sK0 (X1 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [l14 sK0 X0]
  have l18 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [← l16 X0 sK0 sK0]
  have l19 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [← l7 X0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0 X0]
    conv => enter [1, 2]; rw [← l12 sK0]
  have l22 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l21 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41642 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41642 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l25 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41642 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41642 (sK1 ◇ sK0) sK1 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l25 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l28 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l29 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h41642 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41642 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l32 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1, 2, 2, 2]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h41642 ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) sK1 X0]
  have l33 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l32 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))]
  have l34 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l33 sK1 X0 sK0]
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l35 : ∀ sK1 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l34 sK1 X0 sK0]
    conv => enter [1]; rw [← l29 sK0 (sK1 ◇ sK0) sK1]
  have l36 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l35 sK1 sK1 sK0]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l36 sK1 sK0]
  have l38 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 X0 sK0 sK1]
    conv => enter [1]; rw [l6 X0 sK1 sK0]
  have l40 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41642 X0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 X0 sK0 sK1]
  have l41 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [l8 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ X0) X1]
  have l42 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l41 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ sK0) X0 X1]
  have l43 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l40 X0 X0 sK0]
    conv => enter [1]; rw [← l28 sK0 (X0 ◇ X0) X0]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l38 sK0 X0 sK1]
    conv => enter [1]; rw [l39 sK0 sK1 X0]
  have l45 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l38 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← l42 X0 X1 sK0 sK0]
  have l46 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l45 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l47 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 sK0]
    conv => enter [1]; rw [← l22 sK0 X0 (sK0 ◇ sK0)]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l47 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l49 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l50 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l6 X0 sK1 sK0]
    conv => enter [1]; rw [l43 X0 sK0]
    conv => enter [1, 2]; rw [l6 X0 sK1 sK0]
  have l51 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l50 sK1 sK0 X0]
    conv => enter [1]; rw [← l49 sK0 (sK1 ◇ X0) sK1]
  have l52 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l51 sK1 sK0 X0]
    conv => enter [1]; rw [l46 sK0 sK1 X0]
  have l53 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l44 sK0 X0 sK1]
    conv => enter [1]; rw [l52 sK1 sK0 X0]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l53 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK0]
    conv => enter [1]; rw [← l54 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l55 x y]

@[equational_result]
theorem Equation315_implies_Equation41646 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation41646 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h315 sK0 sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_41646_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41646 : Equation41646 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41646 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41646 X0 X1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X1 ◇ X0) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h41646 X0 X1 X1]
    conv => enter [1]; rw [← h41646 (X1 ◇ X0) X1 X1]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h41646 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ X0)]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l5 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l8 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0]
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l9 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l10 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41646 sK0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41646 (sK1 ◇ (sK1 ◇ sK0)) X0 sK1]
    conv => enter [1, 2, 2]; rw [← h41646 sK0 sK1 sK1]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h41646 sK0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41646 sK0 (sK1 ◇ sK0) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l15 : ∀ X0 sK1 sK0 X1 : G, ((X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [h41646 (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h41646 sK0 X0 sK1]
  have l16 : ∀ sK0 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1)) := by
    intro sK0 X1 X0 sK1
    conv => enter [1, 1]; rw [h41646 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l17 : ∀ sK0 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [l16 sK0 X1 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l18 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [← l15 X0 sK1 sK0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ sK0)) (X0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l20 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l18 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← l7 X0 (sK1 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK1 ◇ sK0)) sK0 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h41646 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l11 sK0 sK0]
  have l23 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41646 (sK1 ◇ (sK1 ◇ sK0)) X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l11 sK0 sK1]
  have l24 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0 sK1]
    conv => enter [1]; rw [l20 sK1 (sK0 ◇ sK0) sK0 sK1]
  have l26 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← l24 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l26 sK1 sK0]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l22 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l29 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1, 2]; rw [← l22 sK0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l10 sK0]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) X0]
  have l32 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l31 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1, 2]; rw [← l22 sK0]
  have l34 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l32 sK0 X0]
    conv => enter [1, 2]; rw [← l28 sK0 X0]
  have l35 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK0 ◇ sK0) X0]
  have l36 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l35 sK1 sK0 X0]
  have l37 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41646 sK0 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l29 sK0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l1 sK1 sK0]
  have l39 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l40 : ∀ X1 X2 X0 sK1 sK0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro X1 X2 X0 sK1 sK0
    conv => enter [1]; rw [← h41646 X0 X1 X2]
    conv => enter [1]; rw [l6 X0 sK1 sK0]
  have l41 : ∀ X0 X1 sK1 sK0 : G, ((X0 ◇ X0) ◇ X1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1, 1]; rw [l6 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK0 ◇ X0) X1]
  have l42 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X1))) = ((X0 ◇ X0) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 sK0 X0 X1]
    conv => enter [1]; rw [← l41 X0 X1 sK1 sK0]
  have l43 : ∀ X1 X2 X0 sK0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X2 X0 sK0
    conv => enter [1]; rw [l40 X1 X2 X0 X1 sK0]
    conv => enter [1]; rw [← l39 sK0 X0 X1]
  have l44 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l42 sK1 sK0 X0 X1]
  have l45 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l39 sK0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← l44 X0 X1 sK0 sK0]
  have l46 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h41646 ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) X0 (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK1 sK0]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 (sK1 ◇ (sK0 ◇ sK0)) sK0 sK1]
    conv => enter [1]; rw [← l46 sK1 sK0 sK0]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0)) ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0)))]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1]
    conv => enter [1, 2]; rw [← l21 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l36 sK1 sK0 (sK0 ◇ sK0)]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l22 sK0]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l53 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [l45 sK0 sK1 (sK0 ◇ sK0)]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l53 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l54 sK1 sK0]
  have l56 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 (sK0 ◇ X0) sK0]
    conv => enter [1, 2]; rw [← l6 X0 sK0 sK0]
  have l57 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41646 X0 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l24 sK0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) sK1]
  have l58 : ∀ sK1 sK0 X0 X1 : G, (((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) = (X1 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h41646 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK0 X0 sK1]
  have l59 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l43 sK0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l58 sK1 sK0 X0 sK0]
  have l60 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l57 X0 sK0 X0]
    conv => enter [1]; rw [← l17 sK0 X0 (sK0 ◇ sK0) X0]
  have l61 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [l56 sK0 X0]
  have l62 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l59 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) X0 ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0)]
  have l63 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l34 sK0 X0]
    conv => enter [1]; rw [l61 sK0 X0]
  have l64 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l62 sK0 X0 sK1]
    conv => enter [1]; rw [← l7 (sK1 ◇ (sK1 ◇ sK0)) X0]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41646 sK0 sK1 sK1]
    conv => enter [1]; rw [← h41646 (sK1 ◇ sK0) sK1 sK1]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h41646 (sK1 ◇ sK0) sK1 sK1]
    conv => enter [1]; rw [← h41646 (sK1 ◇ (sK1 ◇ sK0)) sK1 sK1]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l66 sK1 sK0]
    conv => enter [1]; rw [l60 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l65 sK1 sK0]
    conv => enter [1]; rw [l60 (sK1 ◇ sK0) sK0]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l67 sK1 sK0]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l68 sK1 sK0]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (sK1 ◇ sK0)]
  have l72 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ sK0) X0]
  have l73 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l71 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0) X0]
  have l74 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41646 X0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l72 sK0 ((sK1 ◇ sK0) ◇ X0) sK1]
  have l75 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l74 X0 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l76 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h41646 X0 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [← l73 sK0 ((sK1 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0))) sK1]
  have l77 : ∀ sK0 X1 X0 sK1 : G, ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [l72 sK0 (X1 ◇ (X1 ◇ X0)) sK1]
    conv => enter [1]; rw [← l76 sK1 sK0 X0 X1]
  have l78 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l64 sK0 X0 sK0]
    conv => enter [1]; rw [← l77 sK0 X1 X0 sK0]
  have l79 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l63 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X0) X1]
  have l80 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l79 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l81 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l80 sK0 X0 X1]
    conv => enter [1]; rw [← l78 sK0 X1 X0]
  have l82 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l81 sK0 X0 X1]
  have l83 : ∀ X0 X1 sK0 sK1 : G, ((X0 ◇ X0) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK1 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [l75 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK1 ◇ sK0) ◇ X0) X1]
  have l84 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l82 sK0 ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1]; rw [← l83 X0 X1 sK0 sK0]
  have l85 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l84 X0 X1 sK0]
  have l86 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l85 sK1 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0]
    conv => enter [1]; rw [← l86 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l87 x y]

theorem Equation315_4512_implies_Equation41650 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41650 G := by
  have l0 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1, 2]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [← h315 (sK1 ◇ sK1) sK1]
  have l1 : ∀ sK1 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h315 sK1 sK1]
    conv => enter [1]; rw [l0 sK1]
  have l2 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h315 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [h315 (sK3 ◇ (sK0 ◇ sK1)) (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h315 (sK3 ◇ (sK0 ◇ sK1)) sK2]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← h315 sK1 sK0]
  have l4 : ∀ sK3 sK0 sK1 : G, ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK3 ◇ (sK0 ◇ sK1))) = (sK3 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK3 sK0 sK1
    conv => enter [1]; rw [h315 (sK3 ◇ (sK0 ◇ sK1)) sK3]
    conv => enter [1, 2]; rw [← h315 (sK0 ◇ sK1) sK3]
  have l5 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = (sK3 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h315 (sK3 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [l4 sK3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l8 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l10 : ∀ X0 sK1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1]; rw [h315 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 X0]
  have l11 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1, 2]; rw [l10 (sK0 ◇ sK1) sK1]
  have l12 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [l9 sK0 sK1 (sK0 ◇ sK1)]
  have l13 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l13 sK1 sK0]
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) sK1]
  have l15 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l5 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l16 : ∀ sK0 sK1 sK3 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK3 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK3 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK1) (sK3 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l15 sK2 sK3 sK0 sK1]
  have l17 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l2 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1 sK3 sK2]
  have l18 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l10 (sK0 ◇ sK1) sK1]
  have l19 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l18 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l19 x y z w]

theorem Equation4512_41650_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41650 : Equation41650 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h41650 sK0 X0 X1 (sK1 ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK0 sK0]
  have l1 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ X1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [h41650 X1 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (X0 ◇ X1)]
  have l2 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ X1) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X1)) := by
    intro X1 sK1 sK0 X0
    conv => enter [1]; rw [l1 X1 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) (X0 ◇ X1)]
  have l3 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41650 (sK0 ◇ sK0) sK0 sK0 sK0]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h41650 (sK0 ◇ sK0) X0 X0 sK0]
    conv => enter [1, 2]; rw [← h41650 sK0 X0 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l6 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l2 X0 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 X0 (X0 ◇ (X0 ◇ sK0))]
  have l8 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ X1) = (X2 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h41650 X1 X2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l6 sK0 (X0 ◇ X1) X2]
  have l9 : ∀ X1 sK0 X0 : G, (X1 ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l8 X1 X1 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (X0 ◇ X1) X1]
  have l10 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l9 X1 sK0 X0]
    conv => enter [1]; rw [l7 X1 sK0]
  have l11 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [l9 X1 sK0 X0]
  have l12 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l11 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
  have l13 : ∀ sK0 X2 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (X1 ◇ (X1 ◇ X2)) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ X1) X2]
    conv => enter [1]; rw [← l12 X1 X2 sK0 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l13 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

theorem Equation315_4512_implies_Equation41663 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41663 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← h315 sK0 sK2]
  have l3 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [l2 sK2 sK0]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h315 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ sK0) sK0]
  have l5 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h315 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) sK1]
    conv => enter [1, 2]; rw [← h315 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l6 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← l3 sK0 sK2]
  have l7 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [l6 sK0 sK2]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l8 X0 sK0]
  have l10 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h315 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [l8 (sK0 ◇ (sK2 ◇ sK0)) sK0]
  have l11 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l8 X0 sK0]
  have l12 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l11 sK0 X0 X1]
  have l13 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l12 X0 X1 sK0]
    conv => enter [1]; rw [l9 X0 X1 sK0]
  have l14 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK0 sK2
    conv => enter [1]; rw [h315 (sK0 ◇ (sK2 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l10 sK2 sK0]
  have l15 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [l13 sK0 sK2 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l16 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h315 (sK0 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [l15 sK0 sK2]
  have l17 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h315 (sK2 ◇ sK0) sK0]
  have l18 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l17 sK2 sK0]
    conv => enter [1]; rw [l4 sK0 sK2]
    conv => enter [1, 2]; rw [← l17 sK2 sK0]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2]
    conv => enter [1, 2]; rw [← l17 sK2 sK0]
  have l20 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK2 ◇ sK0)]
    conv => enter [1, 2]; rw [← l18 sK2 sK0]
  have l21 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l18 sK2 sK0]
    conv => enter [1]; rw [← l20 sK2 sK0]
  have l22 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l21 sK2 sK0]
    conv => enter [1]; rw [l8 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0]
  have l23 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l22 sK2 sK0]
    conv => enter [1]; rw [← l16 sK2 sK0]
  have l24 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [← l23 sK2 sK0]
  have l25 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1, 2, 1]; rw [← l24 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK2]
  have l26 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0]
  have l27 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l24 sK0 sK2]
    conv => enter [1]; rw [← l26 sK1 sK2 sK0]
  have l28 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [l8 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) sK0]
  have l29 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
  have l30 : ∀ sK0 X0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [← l13 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) X0]
    conv => enter [1]; rw [← l29 sK1 sK2 sK0 X0]
  have l31 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l5 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [← l30 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1 sK2]
  have l33 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l16 sK2 sK0]
    conv => enter [1]; rw [← l32 sK1 sK2 sK0]
  have l34 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l33 sK2 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) sK1 sK2]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l28 sK1 sK2 sK0]
    conv => enter [1]; rw [← l34 sK2 sK0 sK1]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK2]
    conv => enter [1]; rw [← l35 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

theorem Equation4512_41663_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41663 : Equation41663 G) : Equation315 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h41663 sK0 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h41663 X0 (X1 ◇ X2) X3]
    conv => enter [1]; rw [← h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ X0)))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1 X0 X0]
    conv => enter [1, 2]; rw [← h41663 X0 X0 X0]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1]; rw [← l2 (sK1 ◇ sK0) sK0]
  have l4 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l3 sK0 sK0]
    conv => enter [1]; rw [l2 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l6 : ∀ X0 X2 X1 : G, ((X0 ◇ X0) ◇ X2) = (X1 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X1 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l8 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ sK0) sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l11 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h41663 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l8 sK0 X0 X0]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 X0 sK0]
    conv => enter [1]; rw [← l7 (sK0 ◇ sK0) X0 X0]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l12 X0 sK0]
    conv => enter [1]; rw [← l8 sK0 X0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l13 X0 sK0]
  have l15 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l14 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l16 x y]

theorem Equation315_4512_implies_Equation41676 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41676 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h315 sK0 sK0]
    conv => enter [1]; rw [l0 sK0]
  have l2 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2, 2]; rw [← h315 sK0 sK1]
    conv => enter [1]; rw [← h315 (sK0 ◇ sK0) sK2]
  have l3 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l2 sK2 sK1 sK0]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h315 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK2]
    conv => enter [1, 2]; rw [← l3 sK0 sK2 sK1]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← h315 sK0 sK1]
    conv => enter [1]; rw [← l4 sK2 sK1 sK0]
  have l6 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK1 sK0]
    conv => enter [1]; rw [h315 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l7 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h315 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1]; rw [h315 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [h315 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK0]
    conv => enter [1]; rw [← h315 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK1]
  have l9 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK0) X0]
    conv => enter [1, 1, 2]; rw [h315 sK0 sK1]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h315 X0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 X0]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h315 X0 X1]
    conv => enter [1]; rw [l10 X0 sK0]
  have l12 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l5 sK2 sK1 sK0]
    conv => enter [1]; rw [l10 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  have l13 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [l10 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) sK0]
  have l14 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1, 1]; rw [← l10 X0 sK0]
  have l15 : ∀ X0 X1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l14 sK0 X0 X1]
  have l16 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l15 X0 X1 sK0]
    conv => enter [1]; rw [l11 X0 X1 sK0]
  have l17 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1, 1]; rw [l12 sK2 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
  have l18 : ∀ sK0 X0 sK2 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [← l16 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) X0]
    conv => enter [1]; rw [← l17 sK2 sK1 sK0 X0]
  have l19 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
    conv => enter [1]; rw [← l18 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) sK2 sK1]
  have l20 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l19 sK1 sK2 sK0]
    conv => enter [1]; rw [l16 sK0 sK1 (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))]
  have l21 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l13 sK1 sK2 sK0]
    conv => enter [1]; rw [← l20 sK1 sK2 sK0]
  have l22 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
    conv => enter [1]; rw [← l21 sK1 sK2 sK0]
  have l23 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l12 sK2 sK1 sK0]
    conv => enter [1]; rw [l9 sK2 sK0 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l24 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l23 sK2 sK1 sK0]
    conv => enter [1]; rw [h315 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l25 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
    conv => enter [1]; rw [← l24 sK2 sK1 sK0]
  have l26 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 sK2 sK1]
    conv => enter [1]; rw [← l25 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l26 x z y]
  conv => enter [1]; rw [l22 z y x]

theorem Equation4512_41676_implies_Equation315 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h41676 : Equation41676 G) : Equation315 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X1 ◇ X0))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h41676 (X1 ◇ (X1 ◇ X0)) X1 X2]
    conv => enter [1, 2, 2]; rw [← h41676 X0 X1 X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h41676 (X1 ◇ X0) X1 X1]
    conv => enter [1, 2]; rw [← h41676 X0 X1 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X1 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X0) (X1 ◇ (X1 ◇ X0))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h41676 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← l4 X1 X2 X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ sK0) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h41676 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41676 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ (sK1 ◇ sK0))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41676 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK1 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h41676 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [h41676 sK0 sK0 sK0]
    conv => enter [1]; rw [← h41676 (sK0 ◇ sK0) sK0 sK0]
  have l12 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [h41676 sK0 sK0 X0]
    conv => enter [1]; rw [l0 sK1 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h41676 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l14 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l12 sK1 sK0 X0]
    conv => enter [1]; rw [← l9 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK0]
    conv => enter [1]; rw [← l14 sK1 sK0 sK0]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1, 2]; rw [← l15 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK0 (sK0 ◇ sK0)]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1]; rw [← l9 sK0 (sK0 ◇ sK0) sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [← l19 sK1 sK0]
  have l21 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0 sK0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41676 sK0 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l21 sK0]
  have l23 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X1 X0
    conv => enter [1, 2, 2, 2]; rw [l22 sK0 X0]
    conv => enter [1]; rw [← h41676 (X0 ◇ (sK0 ◇ sK0)) sK0 X1]
  have l24 : ∀ sK0 X1 X0 : G, (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l23 sK0 X1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [l3 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l24 sK0 X1 X0]
  have l26 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h41676 sK0 sK0 sK0]
    conv => enter [1]; rw [← l25 X0 sK0 sK0]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0]
    conv => enter [1, 2]; rw [← l11 sK0]
  have l28 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l27 sK0 X0]
    conv => enter [1, 2]; rw [← l21 sK0]
  have l29 : ∀ sK0 X1 X0 : G, ((sK0 ◇ sK0) ◇ X1) = (X0 ◇ ((sK0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l28 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l30 : ∀ sK1 X0 X1 sK0 X2 : G, (sK1 ◇ ((X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro sK1 X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 sK1 (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X2]
    conv => enter [1, 1]; rw [← l6 sK0 sK1 X0 X1]
  have l31 : ∀ sK0 X2 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (sK1 ◇ (X0 ◇ ((X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X2))) := by
    intro sK0 X2 sK1 X0 X1
    conv => enter [1]; rw [← l30 sK1 X0 X1 sK0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X2]
  have l32 : ∀ sK0 X2 sK1 X0 X1 : G, ((sK0 ◇ sK0) ◇ X2) = (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X2)))) := by
    intro sK0 X2 sK1 X0 X1
    conv => enter [1]; rw [l31 sK0 X2 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (sK1 ◇ (sK1 ◇ sK0)) X2]
  have l33 : ∀ sK1 X0 sK0 X1 : G, (sK1 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X1)) = (((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) ◇ X1) := by
    intro sK1 X0 sK0 X1
    conv => enter [1]; rw [h4512 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) X1]
    conv => enter [1, 1]; rw [← h41676 (sK1 ◇ sK0) sK1 X0]
  have l34 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) = (sK1 ◇ ((X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) ◇ X1)) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [← l33 sK1 X0 sK0 X1]
  have l35 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) = (sK1 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l34 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) X1]
  have l36 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK0)) ◇ X1)))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [l35 sK1 sK0 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK0)) X1]
  have l37 : ∀ sK1 sK0 X1 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK1 sK0 X1
    conv => enter [1]; rw [l36 sK1 sK0 X1 sK1]
    conv => enter [1]; rw [← l32 sK0 X1 sK1 sK1 sK1]
  have l38 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1, 2]; rw [h41676 X0 (sK1 ◇ sK0) X1]
    conv => enter [1]; rw [l37 sK1 sK0 (X1 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)))]
  have l39 : ∀ X0 sK0 sK1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h41676 X0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l37 sK1 sK0 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l40 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l39 X0 sK0 X0]
    conv => enter [1, 2]; rw [l37 X0 sK0 X0]
  have l41 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) = ((sK0 ◇ sK0) ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l38 sK1 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l37 sK1 sK0 X0]
  have l42 : ∀ X0 sK0 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [l40 X0 sK0]
    conv => enter [1]; rw [← l29 sK0 X0 (sK0 ◇ sK0)]
  have l43 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 2]; rw [l29 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l41 sK1 sK0 X0 (sK0 ◇ sK0)]
  have l44 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l29 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 X0 sK1]
  have l45 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l44 sK0 (X0 ◇ X1) sK1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l46 : ∀ sK0 X0 X1 sK1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l45 sK0 X0 X1 sK1]
    conv => enter [1, 2]; rw [← l3 X0 X1]
  have l47 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = (X1 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l46 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← l5 X1 (sK0 ◇ sK0) X0]
  have l48 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l47 sK0 X0 X1]
    conv => enter [1]; rw [l42 X1 sK0]
  have l49 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = (((sK0 ◇ sK0) ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [h4512 X1 X1 X2]
    conv => enter [1, 1]; rw [← l47 sK0 X0 X1]
  have l50 : ∀ X1 X2 sK0 X0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X2 sK0 X0
    conv => enter [1]; rw [l49 X1 X2 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ X1) X2]
  have l51 : ∀ X1 X2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = ((sK0 ◇ sK0) ◇ X2) := by
    intro X1 X2 sK0
    conv => enter [1]; rw [l50 X1 X2 sK0 X1]
    conv => enter [1]; rw [l48 sK0 (X1 ◇ X1) X2]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK0]
    conv => enter [1]; rw [← l52 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l53 x y]

theorem Equation315_4512_implies_Equation41680 (G : Type*) [Magma G] (h315 : Equation315 G) (h4512 : Equation4512 G) : Equation41680 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h315 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

end Semigroup5
