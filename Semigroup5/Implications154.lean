import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_4751_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4751 : Equation4751 G) : Equation4 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4751 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4751 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4751 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ X0))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 ((sK0 ◇ sK1) ◇ sK1) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1 sK1]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4751 sK0 sK0]
    conv => enter [1, 2, 2, 2]; rw [l12 sK0 sK1]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l12 sK0 sK1]
  have l15 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l14 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l15 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l17 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) X0]
  have l18 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l17 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) X0]
  have l19 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l18 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 ((sK0 ◇ sK1) ◇ sK0) X0]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l19 sK0 X0 sK1]
    conv => enter [1]; rw [← l16 sK0 sK1 (((sK0 ◇ sK1) ◇ sK0) ◇ X0)]
  have l21 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l20 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 (sK0 ◇ sK1) sK1]
  have l24 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [l24 sK0 sK1]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [l26 sK0 sK1 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l26 sK0 sK1 (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l30 sK0 sK1]
  have l32 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l30 sK0 sK1]
  have l33 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l32 sK1 sK0]
    conv => enter [1, 2]; rw [l26 sK0 sK1 (sK0 ◇ sK1)]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1, 2]; rw [l26 sK0 sK1 (sK0 ◇ sK1)]
  have l35 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK1) sK1]
  have l38 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l36 sK0 sK1]
  have l40 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1, 2]; rw [l26 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ sK1) sK1]
  have l42 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l42 x y]

@[equational_result]
theorem Equation4_implies_Equation4752 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4752 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (y ◇ z))))]

theorem Equation4512_4752_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4752 : Equation4752 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4752 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4752 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4754 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4754 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (z ◇ y))))]

theorem Equation4512_4754_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4754 : Equation4754 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4754 X0 X2 X1]
    conv => enter [1]; rw [← h4754 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X2]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4754 X0 X0 X1]
    conv => enter [1]; rw [← h4754 X0 (X0 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 X0]
    conv => enter [1]; rw [← h4754 X1 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l8 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l6 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation4_implies_Equation4755 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4755 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (z ◇ z))))]

theorem Equation4512_4755_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4755 : Equation4755 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4755 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h4755 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4755 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4755 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [← h4755 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l3 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l7 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l7 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4755 X0 X1 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4755 (sK0 ◇ sK1) sK0 sK0]
    conv => enter [1, 2]; rw [← l8 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation4_implies_Equation4756 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4756 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (z ◇ w))))]

theorem Equation4512_4756_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4756 : Equation4756 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4756 X0 X1 X2 X3]
  have l1 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l0 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X2 ◇ X3))) X4]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X2 ◇ X3)) X4]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l4 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l3 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [← h4756 X0 X0 (X0 ◇ X0) X4]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4758 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4758 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (x ◇ y))))]

theorem Equation4512_4758_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4758 : Equation4758 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK1 ◇ X0) ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4758 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h4758 X2 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4758 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X2 X0 X1]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0]
    conv => enter [1]; rw [l4 X0 X1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)))))]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation4_implies_Equation4759 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4759 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (x ◇ z))))]

theorem Equation4512_4759_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4759 : Equation4759 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4759 X0 X1 X1]
    conv => enter [1]; rw [← h4759 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4759 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ X0)))]
  have l2 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ X0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4761 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4761 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (y ◇ y))))]

theorem Equation4512_4761_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4761 : Equation4761 G) : Equation4 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4761 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4761 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4761 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ X0))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK0))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4761 X0 (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4761 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation4_implies_Equation4762 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4762 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (y ◇ z))))]

theorem Equation4512_4762_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4762 : Equation4762 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4762 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4762 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4764 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4764 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (z ◇ y))))]

theorem Equation4512_4764_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4764 : Equation4764 G) : Equation4 G := by
  have l0 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h4764 X1 (sK1 ◇ X0) sK0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4764 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h4764 X1 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4764 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2))))]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l4 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2]; rw [h4512 sK1 X0 (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
    conv => enter [1]; rw [l0 X1 sK1 X0 sK0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l1 X2 X0]
  have l6 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l4 X1 sK1 X0 sK0]
  have l7 : ∀ X1 sK1 X0 : G, (X1 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ X0))))) = X1 := by
    intro X1 sK1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l1 X0 (X1 ◇ sK1)]
    conv => enter [1]; rw [l6 X1 sK1 X0 X1]
  have l8 : ∀ X1 sK1 : G, (X1 ◇ sK1) = X1 := by
    intro X1 sK1
    conv => enter [1]; rw [l5 X1 sK1 X1]
    conv => enter [1]; rw [l7 X1 sK1 X1]
  intro x y
  conv => enter [1]; rw [← l8 x y]

@[equational_result]
theorem Equation4_implies_Equation4765 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4765 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (z ◇ z))))]

theorem Equation4512_4765_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4765 : Equation4765 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X1) = ((X1 ◇ X1) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h4765 (X1 ◇ X1) X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← h4765 X0 (X1 ◇ X1) X1]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4765 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ X2))) X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X1 X0]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [l3 X2 X3]
    conv => enter [1]; rw [← l6 X0 X3 X1 X2]
  have l8 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [← l7 X0 X0 X0 X3]
    conv => enter [1]; rw [← h4765 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [← l8 x y]

@[equational_result]
theorem Equation4_implies_Equation4766 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4766 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ (z ◇ w))))]

theorem Equation4512_4766_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4766 : Equation4766 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4766 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4766 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4766 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (X0 ◇ X1)))]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ X1)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4768 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4768 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (x ◇ y))))]

theorem Equation4512_4768_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4768 : Equation4768 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ (X3 ◇ X0)))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4768 X0 X1 X2]
    conv => enter [1]; rw [← h4768 X0 (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4768 X0 X2 X1]
    conv => enter [1]; rw [← h4768 X0 (X1 ◇ (X0 ◇ X2)) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ (X3 ◇ X0))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ (X2 ◇ (X0 ◇ X1))) (X0 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X3 ◇ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X2 ◇ (X0 ◇ X1)) (X0 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l4 X0 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l5 X0 X1 X0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [← h4768 X1 X0 X0]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l11 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l9 (sK0 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1]; rw [← l10 sK0 X0 sK1]
  have l12 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l9 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation4_implies_Equation4769 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4769 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (x ◇ z))))]

theorem Equation4512_4769_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4769 : Equation4769 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4769 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4769 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 (X0 ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [← h4769 X1 (X0 ◇ (X1 ◇ X0)) X0]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 (sK0 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 X0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation4_implies_Equation4770 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4770 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (x ◇ w))))]

@[equational_result]
theorem Equation4770_implies_Equation4 (G : Type*) [Magma G] (h4770 : Equation4770 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4770 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4770 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4772 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4772 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (y ◇ y))))]

theorem Equation4512_4772_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4772 : Equation4772 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4772 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4772 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4772 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l2 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4773 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4773 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (y ◇ z))))]

theorem Equation4512_4773_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4773 : Equation4773 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4773 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l5 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4773 sK1 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (X0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK1)))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [l5 sK1 sK0]
    conv => enter [1]; rw [← h4773 X0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1))))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2, 2]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [l6 X0 sK1 sK0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)))))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l7 X0 sK1 sK0]
  have l9 : ∀ X0 sK1 : G, (X0 ◇ sK1) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [l4 X0 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [l8 X0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4_implies_Equation4774 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4774 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (y ◇ w))))]

@[equational_result]
theorem Equation4774_implies_Equation4 (G : Type*) [Magma G] (h4774 : Equation4774 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4774 X0 X1 X0 X1]
    conv => enter [1]; rw [← h4774 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4776 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4776 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (z ◇ y))))]

theorem Equation4512_4776_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4776 : Equation4776 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4776 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4776 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (X0 ◇ (sK0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← h4776 X0 sK0 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l5 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4776 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l7 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ (((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [← l5 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ sK1))) X1]
  have l8 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l7 X0 X1 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (X0 ◇ (sK0 ◇ sK1)) X1]
  have l9 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1)))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l8 X0 X1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2, 2]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [← h4776 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l11 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ sK1)) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l9 X0 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [l10 X0 sK0 sK1]
  have l12 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ X0)) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [← l11 X0 sK0 sK1]
    conv => enter [1]; rw [l5 X0 sK0 sK1]
  have l13 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ X0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [← l11 X0 sK0 X0]
    conv => enter [1]; rw [l2 X0 sK0 X0]
  have l14 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1, 1]; rw [← l11 X0 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK1) X1]
  have l15 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l14 X0 X0 X0 X0]
    conv => enter [1]; rw [l12 X0 X0 X0]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4776 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK0]
    conv => enter [1, 2, 2]; rw [l15 (sK0 ◇ (sK0 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l13 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l19 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation4_implies_Equation4777 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4777 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (z ◇ z))))]

theorem Equation4512_4777_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4777 : Equation4777 G) : Equation4 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4777 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l3 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ (sK0 ◇ sK0)))) = X0 := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [l2 sK0]
    conv => enter [1]; rw [← h4777 X0 X1 sK0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (X0 ◇ sK0))) = X0 := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2, 2]; rw [l2 sK0]
    conv => enter [1]; rw [l3 X0 X1 sK0]
  have l5 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l4 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l8 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l5 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation4_implies_Equation4778 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4778 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4778_implies_Equation4 (G : Type*) [Magma G] (h4778 : Equation4778 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4778 X0 X1 X0 X1]
    conv => enter [1]; rw [← h4778 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4780 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4780 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (w ◇ y))))]

theorem Equation4512_4780_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4780 : Equation4780 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4780 (X0 ◇ X1) X1 X1 X0]
    conv => enter [1]; rw [← h4780 X1 (X0 ◇ X1) (X0 ◇ X1) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h4780 X1 X0 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l3 (sK0 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1]; rw [← l4 sK0 X0 sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation4_implies_Equation4781 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4781 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (w ◇ z))))]

theorem Equation4512_4781_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4781 : Equation4781 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4781 (X0 ◇ X1) X2 X1 X0]
    conv => enter [1]; rw [← h4781 X2 (X0 ◇ X1) (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ X3)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4781 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X4 ◇ X3))))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X4 ◇ X3))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ (X4 ◇ X3))]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4782 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4782 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (w ◇ w))))]

@[equational_result]
theorem Equation4782_implies_Equation4 (G : Type*) [Magma G] (h4782 : Equation4782 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4782 X0 X1 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h4782 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4783 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4783 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ (w ◇ u))))]

@[equational_result]
theorem Equation4783_implies_Equation4 (G : Type*) [Magma G] (h4783 : Equation4783 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4783 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4783 X1 X0 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4785 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4785 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (x ◇ y))))]

theorem Equation4512_4785_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4785 : Equation4785 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4785 X0 X1]
    conv => enter [1]; rw [← h4785 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4785 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4785 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0)))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0)) X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X0 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l9 X0 X0 X0]
    conv => enter [1]; rw [l15 X0 X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l16 X0]
    conv => enter [1]; rw [← h4785 X0 X0]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l16 X0]
    conv => enter [1]; rw [l17 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l18 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l18 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4785 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l24 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l23 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0))]
  have l26 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l24 sK0 X0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)))]
  have l28 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l26 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0))]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ sK0)) sK1]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ sK0)]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ sK0))]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0)]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 ((sK0 ◇ sK1) ◇ sK0) sK1]
  have l35 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4785 sK0 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK1) ◇ sK0) X0]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l38 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l39 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK1 (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l40 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l41 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l42 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l19 sK0 sK1]
  have l43 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [l19 sK0 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2]; rw [← l34 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l42 sK0 sK1]
    conv => enter [1, 2]; rw [← l43 sK0 sK1]
  have l45 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l44 sK0 sK1]
    conv => enter [1]; rw [l18 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l45 x y]

@[equational_result]
theorem Equation4_implies_Equation4786 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4786 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (x ◇ z))))]

@[equational_result]
theorem Equation4786_implies_Equation4 (G : Type*) [Magma G] (h4786 : Equation4786 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4786 X0 X1 X1]
    conv => enter [1]; rw [← h4786 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4786 X0 X0 X0]
    conv => enter [1]; rw [← h4786 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation4_implies_Equation4788 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4788 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (y ◇ y))))]

theorem Equation4512_4788_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4788 : Equation4788 G) : Equation4 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4788 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4788 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4788 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X0))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 ((sK0 ◇ sK1) ◇ sK1) X0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ sK1) ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK0 X0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4788 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l13 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l12 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l13 sK0 sK1 sK1]
  have l24 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l21 sK0 sK1]
  have l25 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l25 x y]

@[equational_result]
theorem Equation4_implies_Equation4789 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4789 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (y ◇ z))))]

theorem Equation4512_4789_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4789 : Equation4789 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4789 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4789 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4791 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4791 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (z ◇ y))))]

theorem Equation4512_4791_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4791 : Equation4791 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4791 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4791 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4791 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4791 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l2 sK1 sK0]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l2 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l6 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l5 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l7 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l8 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4791 sK1 ((sK0 ◇ sK1) ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l4 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 (((sK0 ◇ sK1) ◇ sK1) ◇ sK1)]
  have l10 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [← l7 sK0 (((sK0 ◇ sK1) ◇ sK1) ◇ sK1) sK1]
  have l11 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 sK1]
  have l12 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l11 sK1 sK1]
    conv => enter [1]; rw [← l6 sK1 (sK1 ◇ sK1) sK1]
  have l13 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2, 2, 2]; rw [l12 sK1]
    conv => enter [1]; rw [← h4791 X0 (sK1 ◇ sK1) sK1]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ sK1))))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [l13 X0 sK1]
  have l15 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (X0 ◇ sK1)))))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [l14 X0 sK1]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ sK1) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h4791 sK1 sK1 X0]
    conv => enter [1]; rw [l15 X0 sK1]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1, 1]; rw [l16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation4_implies_Equation4792 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4792 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (z ◇ z))))]

theorem Equation4512_4792_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4792 : Equation4792 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4792 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4792 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h4792 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h4792 X0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h4792 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [← l12 x y]

@[equational_result]
theorem Equation4_implies_Equation4793 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4793 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4793_implies_Equation4 (G : Type*) [Magma G] (h4793 : Equation4793 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4793 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4793 X1 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4793 X0 X0 X0 X0]
    conv => enter [1]; rw [← h4793 X0 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation4_implies_Equation4795 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4795 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ (x ◇ y))))]

theorem Equation4512_4795_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4795 : Equation4795 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4795 X0 X1]
    conv => enter [1]; rw [← h4795 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4795 X0 X1]
  have l2 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4795 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1))) ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1))) ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) X1]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l18 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l19 X0 X1]
  have l21 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l9 X0 X0 X0]
    conv => enter [1]; rw [l20 X0 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l21 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4795 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2, 2, 2]; rw [← l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [← l24 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l26 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l26 x y]

@[equational_result]
theorem Equation4_implies_Equation4796 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4796 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ (x ◇ z))))]

@[equational_result]
theorem Equation4796_implies_Equation4 (G : Type*) [Magma G] (h4796 : Equation4796 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4796 X0 X1 X1]
    conv => enter [1]; rw [← h4796 X1 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4796 X0 X0 X0]
    conv => enter [1]; rw [← h4796 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4799 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4799 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ (y ◇ z))))]

@[equational_result]
theorem Equation4799_implies_Equation4 (G : Type*) [Magma G] (h4799 : Equation4799 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4801 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4801 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ (z ◇ y))))]

theorem Equation4512_4801_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4801 : Equation4801 G) : Equation4 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4801 X0 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4801 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ sK0) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l0 sK0 sK0 X0]
    conv => enter [1]; rw [← h4801 X0 sK0 (sK0 ◇ X0)]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ X0)))) = X1 := by
    intro X1 sK0 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0 sK0]
    conv => enter [1]; rw [← h4801 X1 sK0 X0]
  have l4 : ∀ X0 X1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK0 ◇ X1)) := by
    intro X0 X1 sK0
    conv => enter [1, 1]; rw [← l2 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 sK0 X1]
  have l5 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ (sK0 ◇ X0))) = X1 := by
    intro X1 sK0 X0
    conv => enter [1, 2, 2]; rw [l4 sK0 X0 sK0]
    conv => enter [1]; rw [l3 X1 sK0 X0]
  have l6 : ∀ X1 sK0 X0 : G, (X1 ◇ (sK0 ◇ X0)) = X1 := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [l4 sK0 X0 sK0]
    conv => enter [1]; rw [l5 X1 sK0 X0]
  have l7 : ∀ X0 sK0 X1 X2 : G, (X0 ◇ ((sK0 ◇ X1) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 sK0 X1 X2
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l6 X0 sK0 X1]
  have l8 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (sK0 ◇ X2))) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [← l6 (X0 ◇ X1) sK0 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ X2)]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l4 X1 X2 X0]
    conv => enter [1]; rw [← l8 X0 X1 X0 X2]
  have l10 : ∀ X0 X2 sK0 X1 : G, (X0 ◇ X2) = (X0 ◇ (sK0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 sK0 X1
    conv => enter [1]; rw [← l7 X0 sK0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK0 X1 X2]
  have l11 : ∀ X0 sK0 X2 : G, (X0 ◇ sK0) = (X0 ◇ X2) := by
    intro X0 sK0 X2
    conv => enter [1]; rw [← l9 X0 sK0 (X0 ◇ X2)]
    conv => enter [1]; rw [← l10 X0 X2 sK0 X0]
  have l12 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l11 X0 X2 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l6 sK1 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) sK1 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1, 1]; rw [l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation4_implies_Equation4802 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4802 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ (z ◇ z))))]

@[equational_result]
theorem Equation4802_implies_Equation4 (G : Type*) [Magma G] (h4802 : Equation4802 G) : Equation4 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4802 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) X0 X1]
    conv => enter [1]; rw [← h4802 X2 X3 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X2 X3 : G, (X2 ◇ (X3 ◇ (X3 ◇ X3))) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4802 X3 X2 X2]
    conv => enter [1]; rw [l0 X2 X3 X2 X2]
  have l3 : ∀ X2 X3 : G, (X2 ◇ X3) = X2 := by
    intro X2 X3
    conv => enter [1, 2]; rw [← l1 X3 X3]
    conv => enter [1]; rw [l2 X2 X3]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4803 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4803 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4803_implies_Equation4 (G : Type*) [Magma G] (h4803 : Equation4803 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4805 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4805 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (x ◇ y))))]

theorem Equation4512_4805_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4805 : Equation4805 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4805 X0 X1 X2]
    conv => enter [1]; rw [← h4805 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4805 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X1))) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X1))) ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X1)) X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ X1)) ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 (X0 ◇ X1) ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l8 X0 ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)) X1 X2]
    conv => enter [1]; rw [l9 X0 X1 X2 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X0)))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X1))) (X3 ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l12 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ X1)) (X3 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X1 X2 X3]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 (X0 ◇ X1) (X3 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1 X2 X3]
  have l14 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l15 : ∀ X0 X3 : G, (X0 ◇ (X3 ◇ X0)) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l8 X0 (X3 ◇ X0) X0 X0]
    conv => enter [1]; rw [l14 X0 X0 X0 X3]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l15 X0 X1]
    conv => enter [1]; rw [← h4805 X1 X0 X0]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l15 X0 X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l18 (sK0 ◇ sK1) (sK0 ◇ X0)]
    conv => enter [1]; rw [← l19 sK0 X0 sK1]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l18 sK0 sK0]
    conv => enter [1]; rw [l20 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation4_implies_Equation4806 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4806 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (x ◇ z))))]

theorem Equation4512_4806_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4806 : Equation4806 G) : Equation4 G := by
  have l0 : ∀ sK1 X0 sK0 : G, sK1 = (sK1 ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h4806 sK1 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h4806 X0 sK0 sK1]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4806 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ X2))) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X2)) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X2) X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4806 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4806 ((sK0 ◇ sK1) ◇ sK0) sK1 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l0 sK1 ((sK0 ◇ sK1) ◇ sK0) sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK1 ◇ sK1)]
  have l10 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ ((sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4806 (sK0 ◇ sK1) X0 (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))]
    conv => enter [1, 2, 2, 2, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 ((sK0 ◇ sK1) ◇ sK0) (sK0 ◇ sK1)]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ sK1)]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK0]
    conv => enter [1]; rw [← l6 (sK0 ◇ sK1) (sK0 ◇ sK1) sK0 sK0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [l16 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l18 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1 sK0]
  have l19 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l18 sK1 sK0]
    conv => enter [1, 2]; rw [← l16 sK0 sK1 sK0]
  have l20 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l19 sK1 sK0]
    conv => enter [1, 2]; rw [← l17 sK0 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l22 x y]

@[equational_result]
theorem Equation4_implies_Equation4807 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4807 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (x ◇ w))))]

@[equational_result]
theorem Equation4807_implies_Equation4 (G : Type*) [Magma G] (h4807 : Equation4807 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4807 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4807 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4809 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4809 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (y ◇ y))))]

theorem Equation4512_4809_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4809 : Equation4809 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4809 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) X0 X1]
    conv => enter [1]; rw [← h4809 X2 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4809 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X1 ◇ X1))) X3]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0))) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l0 X2 X0 X1 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ X1)) X3]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l3 X2 X0 X1 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X0) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l5 X2 X0 X1 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X3]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X0 ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l7 X2 X0 X1 X3]
  have l10 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [l8 X2 ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) X0 X1]
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
  have l11 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0))) (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l10 X2 X0 X1 X3]
  have l12 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l11 X2 X0 X1 X3]
  have l13 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X0) (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l12 X2 X0 X1 X3]
  have l14 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X0 (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l13 X2 X0 X1 X3]
  have l15 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l8 X2 (X3 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) X0 X1]
    conv => enter [1]; rw [l14 X2 X0 X1 X3]
  have l16 : ∀ X2 X3 : G, (X2 ◇ X3) = X2 := by
    intro X2 X3
    conv => enter [1, 2]; rw [h4809 X3 X2 X2]
    conv => enter [1]; rw [l15 X2 X3 X2 X2]
  intro x y
  conv => enter [1]; rw [← l16 x y]

@[equational_result]
theorem Equation4_implies_Equation4810 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4810 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (y ◇ z))))]

@[equational_result]
theorem Equation4810_implies_Equation4 (G : Type*) [Magma G] (h4810 : Equation4810 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4810 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X0 X1]
    conv => enter [1]; rw [← h4810 X2 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [h4810 X0 X0 X2]
    conv => enter [1]; rw [l0 X2 X0 X2]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation4811 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4811 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (y ◇ w))))]

@[equational_result]
theorem Equation4811_implies_Equation4 (G : Type*) [Magma G] (h4811 : Equation4811 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4811 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4811 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4813 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4813 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (z ◇ y))))]

theorem Equation4512_4813_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4813 : Equation4813 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4813 X0 X2 X3]
    conv => enter [1]; rw [← h4813 X1 (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4813 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 (X2 ◇ (X3 ◇ (X3 ◇ X2))) ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X3 X0]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X1)) X3]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4512 X2 (X3 ◇ (X3 ◇ X2)) ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X2 ◇ X1) X3]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 (X3 ◇ X2) ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0)))))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X3 X2 ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
  have l10 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l8 X1 ((X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ X0)) X2 X3]
    conv => enter [1]; rw [l9 X1 X2 X3 X0]
  have l11 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 (X2 ◇ (X3 ◇ (X3 ◇ X2))) (X0 ◇ X0)]
    conv => enter [1]; rw [l10 X1 X2 X3 X0]
  have l12 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4512 X2 (X3 ◇ (X3 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l11 X1 X2 X3 X0]
  have l13 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 (X3 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l12 X1 X2 X3 X0]
  have l14 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X3 X2 (X0 ◇ X0)]
    conv => enter [1]; rw [l13 X1 X2 X3 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 (X0 ◇ X0) X1 X1]
    conv => enter [1]; rw [l14 X1 X1 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l15 X0 X0]
    conv => enter [1]; rw [← h4813 X1 X0 X0]
  have l17 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l15 X0 X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← l17 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l18 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 sK1 X0]
  have l21 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation4_implies_Equation4814 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4814 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (z ◇ z))))]

theorem Equation4512_4814_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4814 : Equation4814 G) : Equation4 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h4814 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4814 X0 (X1 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h4814 X1 X0 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4814 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X2 ◇ X2))) X3]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X2 X3 X0 X1]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X2)) X3]
  have l6 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l5 X0 X3 X0 X0]
    conv => enter [1]; rw [l4 X0 X0 (X0 ◇ (X0 ◇ X0)) X3]
  intro x y
  conv => enter [1]; rw [← l6 x y]

@[equational_result]
theorem Equation4_implies_Equation4815 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4815 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4815_implies_Equation4 (G : Type*) [Magma G] (h4815 : Equation4815 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4817 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4817 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (w ◇ y))))]

theorem Equation4512_4817_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4817 : Equation4817 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4817 X0 X2 X3 X4]
    conv => enter [1]; rw [← h4817 X1 (X2 ◇ (X3 ◇ (X4 ◇ X2))) X0 X2]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4817 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X3 ◇ X1))) X4]
  have l3 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0)))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2]; rw [h4512 X2 (X3 ◇ (X4 ◇ X2)) ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0)]
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X0]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X1)) X4]
  have l5 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2]; rw [h4512 X3 (X4 ◇ X2) ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X3 X4 X0]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X3 ◇ X1) X4]
  have l7 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0)))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X4 X2 ((X2 ◇ (X3 ◇ (X4 ◇ X2))) ◇ X0)]
    conv => enter [1]; rw [l5 X1 X2 X3 X4 X0]
  have l8 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 X1 X4]
  have l9 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ X2)) ◇ X0))))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X2 (X3 ◇ (X4 ◇ X2)) X0]
    conv => enter [1]; rw [l7 X1 X2 X3 X4 X0]
  have l10 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ X2) ◇ X0)))))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X3 (X4 ◇ X2) X0]
    conv => enter [1]; rw [l9 X1 X2 X3 X4 X0]
  have l11 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ X0))))))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X4 X2 X0]
    conv => enter [1]; rw [l10 X1 X2 X3 X4 X0]
  have l12 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [l8 X4 X0 X2 X3 X4]
    conv => enter [1]; rw [l11 X1 X2 X3 X4 X0]
  have l13 : ∀ X0 X1 sK1 X2 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (X2 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 X1 sK1 X2 sK0
    conv => enter [1]; rw [h4817 (X0 ◇ X1) sK1 X2 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (X2 ◇ (sK0 ◇ sK1))))]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l12 X0 X1 X0 X0 (X0 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l14 x y]

@[equational_result]
theorem Equation4_implies_Equation4818 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4818 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (w ◇ z))))]

theorem Equation4512_4818_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4818 : Equation4818 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4818 (X0 ◇ X1) (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h4818 X2 (X0 ◇ X1) (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))) X4]
    conv => enter [1, 1]; rw [← h4818 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X2))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ (X3 ◇ X2))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4819 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4819 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (w ◇ w))))]

@[equational_result]
theorem Equation4819_implies_Equation4 (G : Type*) [Magma G] (h4819 : Equation4819 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4819 X0 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h4819 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4820 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4820 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ (w ◇ u))))]

@[equational_result]
theorem Equation4820_implies_Equation4 (G : Type*) [Magma G] (h4820 : Equation4820 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4822 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4822 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (x ◇ y))))]

theorem Equation4512_4822_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4822 : Equation4822 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4822 X0 X1 X2]
    conv => enter [1]; rw [← h4822 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4822 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X0 ◇ X1))) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X3 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X0 ◇ X1))) (X3 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ (X0 ◇ X1)) X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X3 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 (X0 ◇ (X0 ◇ X1)) (X3 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X0))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X3 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X0 ◇ X0)))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l10 : ∀ X0 X3 : G, (X0 ◇ (X3 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l8 X0 (X3 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X0 X3]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [← l10 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [l10 X0 (X0 ◇ X0)]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l10 X0 X0]
    conv => enter [1]; rw [← h4822 X0 X0 X0]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [l10 X0 X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l13 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l15 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l17 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l15 X0]
    conv => enter [1]; rw [l12 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l17 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h4822 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1 X1]
    conv => enter [1]; rw [l18 X0 X1]
  intro x y
  conv => enter [1]; rw [← l19 x y]

@[equational_result]
theorem Equation4_implies_Equation4823 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4823 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (x ◇ z))))]

theorem Equation4512_4823_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4823 : Equation4823 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4823 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4823 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4823 X0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l2 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) X0]
    conv => enter [1, 2]; rw [← h4823 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l4 X2 (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 X2 X0]
    conv => enter [1]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X0 ◇ X2))) X0]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X0 ◇ X2)) X0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l9 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X2) X0]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [l4 X0 (X0 ◇ X2)]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X1 ◇ (X2 ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [← l6 X2 X0 X0]
    conv => enter [1]; rw [l11 X1 X2 X0]
  have l13 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4823 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 sK0 sK1]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l12 (sK0 ◇ sK1) X0 (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation4_implies_Equation4824 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4824 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (x ◇ w))))]

theorem Equation4512_4824_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4824 : Equation4824 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4824 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4824 X1 X2 X0 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4824 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X4))))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X4))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X4)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4826 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4826 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (y ◇ y))))]

@[equational_result]
theorem Equation4826_implies_Equation4 (G : Type*) [Magma G] (h4826 : Equation4826 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4826 (X0 ◇ X0) X0 X1]
    conv => enter [1]; rw [← h4826 X1 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h4826 X1 X0 (X1 ◇ (X0 ◇ X0))]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation4827 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4827 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (y ◇ z))))]

theorem Equation4512_4827_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4827 : Equation4827 G) : Equation4 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h4827 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4827 (X0 ◇ X1) X2 X3]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3))))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0]
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4828 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4828 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (y ◇ w))))]

theorem Equation4512_4828_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4828 : Equation4828 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4828 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4828 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4828 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK0 ◇ (sK1 ◇ X1)))]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4830 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4830 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (z ◇ y))))]

theorem Equation4512_4830_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4830 : Equation4830 G) : Equation4 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4830 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← h4830 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4830 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4830 sK1 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l4 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))]
  have l6 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4830 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4830 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4830 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 2, 2, 2]; rw [← l5 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation4_implies_Equation4831 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4831 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (z ◇ z))))]

theorem Equation4512_4831_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4831 : Equation4831 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4831 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4831 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4831 X0 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h4831 X1 X2 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0]
    conv => enter [1]; rw [l3 X0 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4832 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4832 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4832_implies_Equation4 (G : Type*) [Magma G] (h4832 : Equation4832 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4832 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4832 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4834 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4834 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (w ◇ y))))]

theorem Equation4512_4834_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4834 : Equation4834 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4834 (X0 ◇ X1) X1 X2 X0]
    conv => enter [1]; rw [← h4834 X2 (X0 ◇ X1) X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X2)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4834 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X2))))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X2))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X4 ◇ X2)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4835 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4835 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (w ◇ z))))]

@[equational_result]
theorem Equation4835_implies_Equation4 (G : Type*) [Magma G] (h4835 : Equation4835 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4835 X0 (X1 ◇ X1) X1 X1]
    conv => enter [1]; rw [← h4835 X1 X0 (X1 ◇ X1) X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4836 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4836 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (w ◇ w))))]

theorem Equation4512_4836_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4836 : Equation4836 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4836 X0 X1 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h4836 X1 X2 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4836 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X4 ◇ X4))))]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X4 ◇ X4))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X4 ◇ X4)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4837 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4837 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ (w ◇ u))))]

@[equational_result]
theorem Equation4837_implies_Equation4 (G : Type*) [Magma G] (h4837 : Equation4837 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4837 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4837 X1 X0 X1 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4839 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4839 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (x ◇ y))))]

theorem Equation4512_4839_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4839 : Equation4839 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4839 sK0 (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) = X3 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
    conv => enter [1]; rw [← h4839 X3 X2 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))]
  have l4 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK1) sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4840 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4840 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (x ◇ z))))]

theorem Equation4512_4840_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4840 : Equation4840 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h4840 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4840 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h4840 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0]
    conv => enter [1]; rw [l5 X0]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l6 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 X0]
    conv => enter [1]; rw [← h4840 X0 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l7 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l7 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4840 X0 (X0 ◇ X1) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l7 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l11 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l12 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l9 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l13 X1 X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [← l16 x y]

@[equational_result]
theorem Equation4_implies_Equation4841 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4841 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (x ◇ w))))]

@[equational_result]
theorem Equation4841_implies_Equation4 (G : Type*) [Magma G] (h4841 : Equation4841 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4841 X0 X1 X0 X1]
    conv => enter [1]; rw [← h4841 X1 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4843 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4843 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (y ◇ y))))]

theorem Equation4512_4843_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4843 : Equation4843 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4843 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) X0 X1]
    conv => enter [1]; rw [← h4843 X2 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4843 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X1 ◇ X1))) X3]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0))) (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l0 X2 X0 X1 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X1 ◇ X1)) X3]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X0)) (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l3 X2 X0 X1 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X3]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X0) (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l5 X2 X0 X1 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X3]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X0 (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l7 X2 X0 X1 X3]
  have l10 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l8 X2 (X3 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) X0 X1]
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
  have l11 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0))) (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l10 X2 X3 X0 X1]
  have l12 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l11 X2 X3 X0 X1]
  have l13 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l12 X2 X3 X0 X1]
  have l14 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l13 X2 X3 X0 X1]
  have l15 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2]; rw [l8 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) X0 X1]
    conv => enter [1]; rw [l14 X2 X3 X0 X1]
  have l16 : ∀ X2 X3 : G, (X2 ◇ X3) = X2 := by
    intro X2 X3
    conv => enter [1, 2]; rw [h4843 X3 X2 X2]
    conv => enter [1]; rw [l15 X2 X3 X2 X2]
  intro x y
  conv => enter [1]; rw [← l16 x y]

@[equational_result]
theorem Equation4_implies_Equation4844 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4844 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (y ◇ z))))]

theorem Equation4512_4844_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4844 : Equation4844 G) : Equation4 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4844 X0 X2 X3]
    conv => enter [1]; rw [← h4844 X1 X0 (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X3))))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4844 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 (X3 ◇ (X2 ◇ (X2 ◇ X3))) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X2 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 (X2 ◇ (X2 ◇ X3)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l7 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X2 (X2 ◇ X3) (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X0)))))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X2 X3 (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X0 X2 X3]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l8 X0 X0 X0 X0]
    conv => enter [1]; rw [l9 X1 X0 X0 X0]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X2 (X0 ◇ X1)]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l10 X0 X0]
    conv => enter [1]; rw [← h4844 X1 X0 X0]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l12 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X2 X0 X1]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l17 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l16 X0 X2 X0]
    conv => enter [1]; rw [l15 X0 X0 (X0 ◇ (X0 ◇ X2))]
  intro x y
  conv => enter [1]; rw [← l17 x y]

@[equational_result]
theorem Equation4_implies_Equation4845 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4845 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (y ◇ w))))]

@[equational_result]
theorem Equation4845_implies_Equation4 (G : Type*) [Magma G] (h4845 : Equation4845 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4845 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4845 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4847 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4847 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (z ◇ y))))]

theorem Equation4512_4847_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4847 : Equation4847 G) : Equation4 G := by
  have l0 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ ((sK1 ◇ X0) ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h4847 X1 (sK1 ◇ X0) sK0]
  have l1 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2]; rw [h4512 sK1 X0 (sK0 ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
    conv => enter [1]; rw [l0 X1 sK1 X0 sK0]
  have l2 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l1 X1 sK1 X0 sK0]
  have l3 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))))) = X1 := by
    intro X1 sK1 X0 sK0
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
    conv => enter [1]; rw [l2 X1 sK1 X0 sK0]
  have l4 : ∀ X1 sK1 : G, (X1 ◇ sK1) = X1 := by
    intro X1 sK1
    conv => enter [1, 2]; rw [h4847 sK1 X1 (X1 ◇ sK1)]
    conv => enter [1]; rw [l3 X1 sK1 X1 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4848 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4848 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (z ◇ z))))]

@[equational_result]
theorem Equation4848_implies_Equation4 (G : Type*) [Magma G] (h4848 : Equation4848 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4848 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4848 X1 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4849 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4849 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4849_implies_Equation4 (G : Type*) [Magma G] (h4849 : Equation4849 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4849 X0 X1 X0 X1]
    conv => enter [1]; rw [← h4849 X1 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4851 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4851 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (w ◇ y))))]

theorem Equation4512_4851_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4851 : Equation4851 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4851 (X0 ◇ X1) X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h4851 X2 (X0 ◇ X1) X1 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4851 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ (X3 ◇ X1))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4852 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4852 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (w ◇ z))))]

@[equational_result]
theorem Equation4852_implies_Equation4 (G : Type*) [Magma G] (h4852 : Equation4852 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4852 X0 (X1 ◇ X0) X0 X1]
    conv => enter [1]; rw [← h4852 X1 X0 (X1 ◇ X0) (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4853 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4853 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (w ◇ w))))]

@[equational_result]
theorem Equation4853_implies_Equation4 (G : Type*) [Magma G] (h4853 : Equation4853 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4853 X0 (X1 ◇ X1) X0 X1]
    conv => enter [1]; rw [← h4853 X1 X0 (X1 ◇ X1) (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4854 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4854 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ (w ◇ u))))]

@[equational_result]
theorem Equation4854_implies_Equation4 (G : Type*) [Magma G] (h4854 : Equation4854 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4854 X0 X1 X0 X1 X1]
    conv => enter [1]; rw [← h4854 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4856 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4856 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (x ◇ y))))]

theorem Equation4512_4856_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4856 : Equation4856 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4856 sK0 (sK1 ◇ X0) X1]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ X0))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [← h4856 (sK0 ◇ sK1) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4857 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4857 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (x ◇ z))))]

theorem Equation4512_4857_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4857 : Equation4857 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4857 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4857 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← l0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4857 sK0 X0 sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l4 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0 X0]
    conv => enter [1, 2, 2]; rw [← l1 sK0]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l7 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) = X0 := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2, 2]; rw [l5 sK0 X0]
    conv => enter [1]; rw [← h4857 X0 X1 sK0]
  have l8 : ∀ X0 X1 sK0 : G, (X0 ◇ (X1 ◇ sK0)) = X0 := by
    intro X0 X1 sK0
    conv => enter [1, 2, 2]; rw [l1 sK0]
    conv => enter [1]; rw [l7 X0 X1 sK0]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ sK0) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l6 sK0 X0]
    conv => enter [1]; rw [l8 X0 (sK0 ◇ X0) sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1]; rw [l9 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation4_implies_Equation4858 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4858 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (x ◇ w))))]

@[equational_result]
theorem Equation4858_implies_Equation4 (G : Type*) [Magma G] (h4858 : Equation4858 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4858 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4858 X1 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4860 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4860 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (y ◇ y))))]

theorem Equation4512_4860_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4860 : Equation4860 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4860 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) X0 X1]
    conv => enter [1]; rw [← h4860 X2 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4860 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ (X1 ◇ X1))) X3]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0))) (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l0 X2 X0 X1 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ X1)) X3]
  have l5 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X0)) (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l3 X2 X0 X1 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X0) (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l5 X2 X0 X1 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X3]
  have l9 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))))))))) = X2 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X0 (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l7 X2 X0 X1 X3]
  have l10 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [l8 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) X0 X1]
    conv => enter [1]; rw [l9 X2 X0 X1 X3]
  have l11 : ∀ X2 X3 : G, (X2 ◇ (X3 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [h4860 X3 X2 X2]
    conv => enter [1]; rw [l10 X2 X3 X2 X2]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l11 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [← h4860 X1 X0 (X0 ◇ X0)]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l11 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l12 X1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK1 X0]
    conv => enter [1, 1]; rw [← l13 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l14 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 sK1 X0]
  have l17 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 sK0]
    conv => enter [1]; rw [l14 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation4_implies_Equation4861 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4861 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (y ◇ z))))]

theorem Equation4512_4861_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4861 : Equation4861 G) : Equation4 G := by
  have l0 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4861 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X1 X0]
    conv => enter [1]; rw [← h4861 X2 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))]
    conv => enter [1]; rw [← h4861 X3 (X0 ◇ X1) X2]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l1 X3 X0 X1 X2]
  have l3 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l0 X2 X1 X0]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l3 X2 X1 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X0 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l4 X2 X1 X0]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0 X0 X1 X0]
    conv => enter [1]; rw [l5 X2 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X0 X1 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h4861 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

@[equational_result]
theorem Equation4_implies_Equation4862 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4862 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (y ◇ w))))]

@[equational_result]
theorem Equation4862_implies_Equation4 (G : Type*) [Magma G] (h4862 : Equation4862 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4862 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4862 X1 X0 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4864 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4864 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (z ◇ y))))]

theorem Equation4512_4864_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4864 : Equation4864 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X2)))) ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4864 X0 X2 X3]
    conv => enter [1]; rw [← h4864 X1 (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X2)))) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4864 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4864 X1 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4864 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ (X3 ◇ X2))) ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 (X3 ◇ (X3 ◇ (X3 ◇ X2))) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X3 X0]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ (X2 ◇ X1)) X3]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4512 X3 (X3 ◇ (X3 ◇ X2)) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X2 ◇ X1) X3]
  have l8 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ ((X3 ◇ X2) ◇ (X0 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 (X3 ◇ X2) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X1 X2 X3 X0]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l10 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X3 X2 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l8 X1 X2 X3 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (X0 ◇ (X0 ◇ X0)) X1 X1]
    conv => enter [1]; rw [l10 X1 X1 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l12 x y]

@[equational_result]
theorem Equation4_implies_Equation4865 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4865 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (z ◇ z))))]

theorem Equation4512_4865_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4865 : Equation4865 G) : Equation4 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2)))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4865 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X3 X0 : G, (X3 ◇ X0) = X3 := by
    intro X3 X0
    conv => enter [1, 2]; rw [h4865 X0 X3 X3]
    conv => enter [1]; rw [l0 X3 X0 X3 X3]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation4866 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4866 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (z ◇ w))))]

@[equational_result]
theorem Equation4866_implies_Equation4 (G : Type*) [Magma G] (h4866 : Equation4866 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4866 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4866 X1 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4868 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4868 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (w ◇ y))))]

theorem Equation4512_4868_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4868 : Equation4868 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4868 (X0 ◇ X1) X1 X1 X0]
    conv => enter [1]; rw [← h4868 X2 (X0 ◇ X1) X1 X1]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4868 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ (X3 ◇ X1))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4869 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4869 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (w ◇ z))))]

theorem Equation4512_4869_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4869 : Equation4869 G) : Equation4 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X2)))]
    conv => enter [1]; rw [← h4869 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X4 X0 : G, (X4 ◇ X0) = X4 := by
    intro X4 X0
    conv => enter [1, 2]; rw [h4869 X0 X4 X4 X4]
    conv => enter [1]; rw [l0 X4 X0 X4 X4 X4]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation4870 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4870 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (w ◇ w))))]

@[equational_result]
theorem Equation4870_implies_Equation4 (G : Type*) [Magma G] (h4870 : Equation4870 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4870 X0 (X1 ◇ X1) (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h4870 X1 X0 (X1 ◇ X1) (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4871 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4871 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ (w ◇ u))))]

@[equational_result]
theorem Equation4871_implies_Equation4 (G : Type*) [Magma G] (h4871 : Equation4871 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4871 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4871 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4873 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4873 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (x ◇ y))))]

theorem Equation4512_4873_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4873 : Equation4873 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = (sK0 ◇ ((sK1 ◇ X0) ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4873 sK0 (sK1 ◇ X0) X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = (sK0 ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l0 sK0 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X1 ◇ (X2 ◇ ((sK0 ◇ sK1) ◇ X0))))]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4873 (sK0 ◇ sK1) sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4874 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4874 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (x ◇ z))))]

@[equational_result]
theorem Equation4874_implies_Equation4 (G : Type*) [Magma G] (h4874 : Equation4874 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4874 X0 (X0 ◇ X1) X1 X1]
    conv => enter [1]; rw [← h4874 X1 X0 (X0 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4875 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4875 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (x ◇ w))))]

@[equational_result]
theorem Equation4875_implies_Equation4 (G : Type*) [Magma G] (h4875 : Equation4875 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4875 X0 X1 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h4875 X1 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4876 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4876 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (x ◇ u))))]

@[equational_result]
theorem Equation4876_implies_Equation4 (G : Type*) [Magma G] (h4876 : Equation4876 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4876 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4876 X1 X0 X1 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4878 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4878 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (y ◇ y))))]

theorem Equation4512_4878_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4878 : Equation4878 G) : Equation4 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h4878 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4878 (X0 ◇ X0) X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4878 X1 (X0 ◇ X0) X0 X1]
  have l2 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4878 X0 X1 X2 X3]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ (X1 ◇ X1))) X4]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X3 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X4 X0 X1 X2 X3]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X1)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ (X1 ◇ X1)) X4]
  have l6 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l5 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l4 X0 X0 X0 (X0 ◇ (X0 ◇ X0)) X4]
  intro x y
  conv => enter [1]; rw [← l6 x y]

@[equational_result]
theorem Equation4_implies_Equation4879 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4879 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (y ◇ z))))]

theorem Equation4512_4879_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4879 : Equation4879 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ ((X3 ◇ (X4 ◇ (X2 ◇ X3))) ◇ X0))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4879 X0 X2 X3 X4]
    conv => enter [1]; rw [← h4879 X1 X2 (X3 ◇ (X4 ◇ (X2 ◇ X3))) X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X2)))) X4]
    conv => enter [1, 1]; rw [← h4879 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ (X1 ◇ X2))) X4]
  have l3 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X4 ◇ (X2 ◇ X3)) ◇ X0)))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2]; rw [h4512 X3 (X4 ◇ (X2 ◇ X3)) X0]
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X0]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X3 ◇ (X1 ◇ X2)) X4]
  have l5 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ ((X2 ◇ X3) ◇ X0))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X4 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l3 X1 X2 X3 X4 X0]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 (X1 ◇ X2) X4]
  have l7 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X2 ◇ (X3 ◇ X0)))))) = X1 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X2 X3 X0]
    conv => enter [1]; rw [l5 X1 X2 X3 X4 X0]
  have l8 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4)))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X4]
  have l9 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l8 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l7 X0 X0 X0 X0 X4]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4_implies_Equation4880 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4880 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (y ◇ w))))]

@[equational_result]
theorem Equation4880_implies_Equation4 (G : Type*) [Magma G] (h4880 : Equation4880 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4880 X0 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← h4880 X1 X0 X1 (X1 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4881 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4881 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (y ◇ u))))]

@[equational_result]
theorem Equation4881_implies_Equation4 (G : Type*) [Magma G] (h4881 : Equation4881 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4881 X0 X1 X1 X0 X1]
    conv => enter [1]; rw [← h4881 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4883 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4883 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (z ◇ y))))]

theorem Equation4512_4883_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4883 : Equation4883 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4883 (X0 ◇ X1) X1 X0 X1]
    conv => enter [1]; rw [← h4883 X2 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4883 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ (X2 ◇ X1))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4884 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4884 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (z ◇ z))))]

@[equational_result]
theorem Equation4884_implies_Equation4 (G : Type*) [Magma G] (h4884 : Equation4884 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4884 X0 (X1 ◇ X1) X1 (X1 ◇ X1)]
    conv => enter [1]; rw [← h4884 X1 X0 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4885 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4885 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (z ◇ w))))]

theorem Equation4512_4885_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4885 : Equation4885 G) : Equation4 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h4885 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X4 X0 : G, (X4 ◇ X0) = X4 := by
    intro X4 X0
    conv => enter [1, 2]; rw [h4885 X0 X4 X4 X4]
    conv => enter [1]; rw [l0 X4 X0 X4 X4 X4]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation4886 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4886 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (z ◇ u))))]

@[equational_result]
theorem Equation4886_implies_Equation4 (G : Type*) [Magma G] (h4886 : Equation4886 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4886 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4886 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4888 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4888 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (w ◇ y))))]

theorem Equation4512_4888_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4888 : Equation4888 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4888 (X0 ◇ X1) X1 X0 X0]
    conv => enter [1]; rw [← h4888 X2 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4888 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ (X3 ◇ X1))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4889 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4889 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (w ◇ z))))]

@[equational_result]
theorem Equation4889_implies_Equation4 (G : Type*) [Magma G] (h4889 : Equation4889 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4889 X0 (X1 ◇ X1) X1 X1]
    conv => enter [1]; rw [← h4889 X1 X0 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4890 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4890 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (w ◇ w))))]

theorem Equation4512_4890_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4890 : Equation4890 G) : Equation4 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))))) = X4 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h4890 X4 (X0 ◇ X1) X2 X3]
  have l1 : ∀ X4 X0 : G, (X4 ◇ X0) = X4 := by
    intro X4 X0
    conv => enter [1, 2]; rw [h4890 X0 X4 X4 X4]
    conv => enter [1]; rw [l0 X4 X0 X4 X4 X4]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation4891 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4891 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (w ◇ u))))]

@[equational_result]
theorem Equation4891_implies_Equation4 (G : Type*) [Magma G] (h4891 : Equation4891 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4891 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4891 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4893 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4893 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (u ◇ y))))]

theorem Equation4512_4893_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4893 : Equation4893 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4893 (X0 ◇ X1) X1 X2 X2 X0]
    conv => enter [1]; rw [← h4893 X2 (X0 ◇ X1) X1 X2 X2]
  have l1 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) ◇ X5)) = (X0 ◇ X5) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X1)))) X5]
    conv => enter [1, 1]; rw [← h4893 X0 X1 X2 X3 X4]
  have l2 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ X5) = (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X1))) ◇ X5))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X1))) X5]
  have l3 : ∀ X0 X5 : G, (X0 ◇ X5) = X0 := by
    intro X0 X5
    conv => enter [1]; rw [l2 X0 X5 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X5)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4894 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4894 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (u ◇ z))))]

@[equational_result]
theorem Equation4894_implies_Equation4 (G : Type*) [Magma G] (h4894 : Equation4894 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4894 X0 (X1 ◇ X1) X1 X1 X1]
    conv => enter [1]; rw [← h4894 X1 X0 (X1 ◇ X1) X1 X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4895 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4895 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (u ◇ w))))]

@[equational_result]
theorem Equation4895_implies_Equation4 (G : Type*) [Magma G] (h4895 : Equation4895 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4895 X0 X1 (X1 ◇ X1) X1 X1]
    conv => enter [1]; rw [← h4895 X1 X0 X1 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4896 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4896 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (u ◇ u))))]

@[equational_result]
theorem Equation4896_implies_Equation4 (G : Type*) [Magma G] (h4896 : Equation4896 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4896 X0 X1 X1 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h4896 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4897 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4897 G := by
  intro x y z w u v
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ (u ◇ v))))]

@[equational_result]
theorem Equation4897_implies_Equation4 (G : Type*) [Magma G] (h4897 : Equation4897 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation5_implies_Equation13 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation13 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation13_4512_implies_Equation5 (G : Type*) [Magma G] (h13 : Equation13 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h13 X1 X2]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation19 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation19 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

theorem Equation19_4512_implies_Equation5 (G : Type*) [Magma G] (h19 : Equation19 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h19 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h19 (sK1 ◇ sK0) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation62 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation62 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ x)) y]

theorem Equation62_4512_implies_Equation5 (G : Type*) [Magma G] (h62 : Equation62 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 X0]
    conv => enter [1]; rw [l3 X1 X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h62 X1 X2]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l5 sK0 sK0 sK0]
    conv => enter [1]; rw [← l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation65 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation65 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ x)) y]

theorem Equation65_4512_implies_Equation5 (G : Type*) [Magma G] (h65 : Equation65 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [h65 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l0 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l1 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h65 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ ((sK0 ◇ X0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h65 (sK0 ◇ X0) sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK0 X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK1 ◇ (sK0 ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK1 ◇ sK0) ◇ X0)]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK1 ◇ sK0) ◇ (X0 ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l5 sK0 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (X0 ◇ ((sK1 ◇ sK0) ◇ X0))]
  have l7 : ∀ sK0 X0 : G, (sK0 ◇ X0) = X0 := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0 sK0]
    conv => enter [1]; rw [← h65 X0 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h65 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK0]
    conv => enter [1]; rw [← l9 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation5_implies_Equation68 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation68 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ x)) y]

theorem Equation68_4512_implies_Equation5 (G : Type*) [Magma G] (h68 : Equation68 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h68 (sK1 ◇ sK0) X0 sK0]
    conv => enter [1, 2]; rw [← h68 sK0 (sK1 ◇ sK0) sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h68 (sK0 ◇ (sK1 ◇ sK0)) X0 sK0]
    conv => enter [1, 2, 2]; rw [← h68 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h68 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
  have l4 : ∀ sK0 X0 : G, sK0 = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h68 sK0 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation72 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation72 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2]; rw [h5 (x ◇ x) y]

theorem Equation72_4512_implies_Equation5 (G : Type*) [Magma G] (h72 : Equation72 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h72 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h72 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h72 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h72 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X0 X1]
    conv => enter [1, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l4 sK1 sK0]
    conv => enter [1, 2]; rw [l6 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation5_implies_Equation78 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation78 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ x) y]

theorem Equation78_4512_implies_Equation5 (G : Type*) [Magma G] (h78 : Equation78 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h78 X0 X2 X1]
    conv => enter [1]; rw [← h78 (X1 ◇ X0) X2 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X2 ◇ X3)) X1]
    conv => enter [1]; rw [← h78 X3 X1 X2]
  have l2 : ∀ sK0 X1 X0 sK1 : G, sK0 = (X1 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X1 X0 sK1
    conv => enter [1]; rw [h78 sK0 X0 sK1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (sK1 ◇ sK0)) X1]
  have l3 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X2 ◇ X0) X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X0 (X1 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation82 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation82 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h5 (z ◇ (x ◇ x)) y]

theorem Equation82_4512_implies_Equation5 (G : Type*) [Magma G] (h82 : Equation82 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h82 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2]; rw [← h82 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X1 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h82 X1 X2 X3]
  have l2 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h82 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X2 ◇ X0) X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X0 (X1 ◇ (sK1 ◇ sK0))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation5_implies_Equation86 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation86 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ x)) y]

theorem Equation86_4512_implies_Equation5 (G : Type*) [Magma G] (h86 : Equation86 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X2 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h86 X0 X2 X1]
    conv => enter [1]; rw [← h86 (X2 ◇ X0) X1 X2]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 (X1 ◇ (X2 ◇ X3)) X2]
    conv => enter [1]; rw [← h86 X3 X2 X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h86 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation5_implies_Equation90 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation90 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ x)) y]

theorem Equation90_4512_implies_Equation5 (G : Type*) [Magma G] (h90 : Equation90 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = (X1 ◇ X0) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h90 X0 X1 X1]
    conv => enter [1]; rw [← h90 (X1 ◇ X0) X2 X1]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h90 (sK1 ◇ sK0) X0 sK1]
    conv => enter [1, 2]; rw [← h90 sK0 sK1 sK1]
  have l2 : ∀ sK0 X0 X1 sK1 : G, sK0 = (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [h90 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X1 sK0 sK1]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [l0 X0 (X1 ◇ X2) X1]
    conv => enter [1]; rw [← h90 X2 X3 X1]
  have l4 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [l2 sK0 (X2 ◇ X0) X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X0 (X1 ◇ (sK1 ◇ sK0))]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation5_implies_Equation94 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation94 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  intro x y z w
  conv => enter [1]; rw [l0 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ x)) y]

theorem Equation94_4512_implies_Equation5 (G : Type*) [Magma G] (h94 : Equation94 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ sK0 X2 X0 X1 sK1 : G, sK0 = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X2 X0 X1 sK1
    conv => enter [1]; rw [h94 sK0 (X2 ◇ X0) X1 sK1]
    conv => enter [1]; rw [← h4512 X2 X0 (X1 ◇ (sK1 ◇ sK0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK0 sK0 sK1]
    conv => enter [1]; rw [← h94 (sK1 ◇ sK0) sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation463 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation463 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation463_4512_implies_Equation5 (G : Type*) [Magma G] (h463 : Equation463 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X2))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h463 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h463 X2 X0]
    conv => enter [1]; rw [l0 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation469 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation469 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation469_4512_implies_Equation5 (G : Type*) [Magma G] (h469 : Equation469 G) (h4512 : Equation4512 G) : Equation5 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X2)))]
    conv => enter [1]; rw [← h469 X2 (X0 ◇ X1) X3]
  have l1 : ∀ X0 X2 : G, (X0 ◇ X2) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h469 X2 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation5_implies_Equation476 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation476 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

end Semigroup5
